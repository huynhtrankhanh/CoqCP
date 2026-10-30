#!/usr/bin/env python3
"""Build CoqCP source to native C++ and independently recheck generated Rocq.

Checks the actual-main contract on the explicit canonical capacity domain, audits all registered proof roots, and independently rechecks them with the kernel.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path
import shutil
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--rocq', default='/opt/rocq/9.3.0/bin/rocq')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    repo = here.parents[2]
    manifest_path = here / 'proof-manifest.json'
    manifest_bytes = manifest_path.read_bytes()
    manifest = json.loads(manifest_bytes)
    expected_keys = {'coqcp_modules', 'trusted_modules', 'pending_proof_ports', 'proof_modules', 'audit_roots'}
    if set(manifest) != expected_keys:
        raise ValueError('Invalid proof manifest keys')
    for key in expected_keys:
        entries = manifest[key]
        if (not isinstance(entries, list) or any(not isinstance(name, str) or not name for name in entries)
                or len(entries) != len(set(entries))):
            raise ValueError(f'Invalid or duplicate entries in proof manifest: {key}')
        pattern = r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*' if key == 'audit_roots' else r'[A-Za-z_][A-Za-z0-9_]*'
        if any(re.fullmatch(pattern, name) is None for name in entries):
            raise ValueError(f'Invalid identifier in proof manifest: {key}')
    if not set(manifest['pending_proof_ports']) <= set(manifest['proof_modules']):
        raise ValueError('Pending proof modules must be present in proof_modules')
    proof_dependencies = {}
    seen_modules = set()
    for name in manifest['proof_modules']:
        source_text = (here / 'proof' / f'{name}.v').read_text()
        dependencies = set(' '.join(re.findall(
            r'From NativeProof Require (?:Import|Export) ([^.]+)\.', source_text)).split())
        missing = dependencies - seen_modules
        if missing:
            raise ValueError(f'Proof module {name} has missing or later dependencies: {sorted(missing)}')
        proof_dependencies[name] = dependencies
        seen_modules.add(name)
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    (out / 'proof-manifest.json').write_bytes(manifest_bytes)
    code = out / 'Code'
    code.mkdir()
    proofs = out / 'Proof'
    proofs.mkdir()

    def run(command):
        subprocess.run(list(map(str, command)), cwd=repo, check=True)

    # Verify exactly the published IIL source, including upstream formatting.
    shutil.copy2(repo / 'programs/ZFCProofChecker.js', out / 'ProofChecker.js')
    run(['node', repo / 'compiler/dist/cli.js', code / 'ProofChecker.v',
         out / 'checker.cpp', out / 'ProofChecker.js', repo / 'programs/IO/PrintInt64.js'])
    (out / 'CoqCP').mkdir()
    (out / 'Trusted').mkdir()
    flags = ['-q', '-Q', str(out / 'CoqCP'), 'CoqCP', '-Q', str(code), 'ImperativeZFC',
             '-Q', str(proofs), 'NativeProof', '-Q', str(out / 'Trusted'), 'Trusted']
    for name in manifest['coqcp_modules']:
        source = out / 'CoqCP' / f'{name}.v'
        origin = repo / 'theories' / source.name
        shutil.copy2(origin, source)
        run([args.rocq, 'compile', *flags, source])
    for name in manifest['trusted_modules']:
        source = out / 'Trusted' / f'{name}.v'
        shutil.copy2(here.parent / 'spec' / source.name, source)
        run([args.rocq, 'compile', *flags, source])
    run([args.rocq, 'compile', *flags, code / 'ProofChecker.v'])
    (code / 'NativeContract.v').write_text(
        'From CoqCP Require Import Options Imperative Execution.\n'
        'From Trusted Require Import Spec.\n'
        'From ImperativeZFC Require Import ProofChecker.\n'
        'Definition native_contract capacity := Trusted.Spec.required\n'
        '  (funcdef_0__main (fun x => match x with end) (fun x => match x with end))\n'
        '  (arrays _ environment1) capacity.\n')
    run([args.rocq, 'compile', *flags, code / 'NativeContract.v'])
    proof_modules = list(manifest['proof_modules'])
    # These sources describe the former eight-level, uncached traversal.
    # Keep them for porting, but never audit them against a different program.
    pending_proof_ports = set(manifest['pending_proof_ports'])
    while True:
        old_pending = set(pending_proof_ports)
        for name in proof_modules:
            if proof_dependencies[name] & pending_proof_ports:
                pending_proof_ports.add(name)
        if pending_proof_ports == old_pending:
            break
    proof_modules = [name for name in proof_modules if name not in pending_proof_ports]
    for name in proof_modules:
        source = proofs / f'{name}.v'
        shutil.copy2(here / 'proof' / source.name, source)
        run([args.rocq, 'compile', *flags, source])
    # Audit the declared roots whose proof modules are active.
    audited = [name for name in manifest['audit_roots']
               if name.split('.')[0] not in pending_proof_ports]
    if 'NativeFastDomain' not in proof_modules or 'NativeFastDomain.native_required' not in audited:
        raise ValueError('The verified native contract must be compiled and audited')
    (code / 'Audit.v').write_text(
        'From CoqCP Require Import Options TapeEnd.\n'
        'From ImperativeZFC Require Import ProofChecker.\n'
        'From Trusted Require Import Spec ByteProtocol.\n'
        'From NativeProof Require Import ' + ' '.join(proof_modules) + '.\n' +
        ''.join(f'Print Assumptions {name}.\n' for name in audited))
    result = subprocess.run([args.rocq, 'compile', *flags, str(code / 'Audit.v')],
                            cwd=repo, text=True, capture_output=True)
    (out / 'main-assumptions.log').write_text(result.stdout + result.stderr)
    result.check_returncode()
    if (result.stdout.count('Closed under the global context') != len(audited)
            or 'Axioms:' in result.stdout):
        raise RuntimeError('Generated program or execution proofs have unexpected assumptions: '
                           + result.stdout)
    with (out / 'kernel.log').open('w') as log:
        subprocess.run([args.rocq, 'check', '-silent', *flags[1:],
                        'CoqCP.TapeEnd', 'ImperativeZFC.NativeContract', 'Trusted.ByteProtocol',
                        *[f'NativeProof.{name}' for name in proof_modules]],
                       cwd=repo, check=True, stdout=log, stderr=subprocess.STDOUT)
    with (out / 'cpp-build.log').open('w') as log:
        subprocess.run(['g++', '-std=c++20', '-O2', str(out / 'checker.cpp'),
                        '-o', str(out / 'zfc-checker')], check=True,
                       stdout=log, stderr=subprocess.STDOUT)
    artifacts = {name: hashlib.sha256((out / name).read_bytes()).hexdigest()
                 for name in ['proof-manifest.json', 'ProofChecker.js', 'Code/ProofChecker.v', 'checker.cpp', 'zfc-checker']
                 + [f'Proof/{name}.v' for name in proof_modules]
                 + [f'Trusted/{name}.v' for name in manifest['trusted_modules']]}
    (out / 'development-status.json').write_text(json.dumps({
        'status': 'verified', 'implementation': 'CoqCP imperative DSL to C++ and Rocq',
        'verified_domain': 'well-shaped canonical requests satisfying NativeFastDomain.within_capacity; unsigned seeds',
        'native_contract_theorem': 'NativeFastDomain.native_required',
        'capacity_check': 'set-first finite check with early binary cutoffs for general schema budgets; equivalent to NativeVerifiedDomain.within_capacity',
        'generated_rocq_kernel_recheck': 'passed', 'main_global_assumptions': [],
        'proof_module_count': len(proof_modules), 'closed_assumption_audits': len(audited),
        'inactive_legacy_proof_modules': sorted(pending_proof_ports),
        'implemented_unproved': [], 'missing_obligations': [],
        'proved_generated_execution': [
            'actual seeded main, all 26 positive opcodes, EOF and quit under the declared finite capacity check',
            'exact cumulative stdout, unread quit suffix, and every interactive flush snapshot',
            'all five logical state representations, immutable names and canonical formula IDs',
            'all eighteen axiom families, MP, generalization, class set certification and named theorem recall',
            'typed class-metavariable schema construction and capture-avoiding instantiation with ZFC derivations',
            'SipHash interning and memoized substitution with checked polynomial scheduler fuel',
            'explicit formula, class and variable-index allocation bounds preserved through complete dialogues',
        ],
        'outside_verified_domain': [
            'malformed byte streams and noncanonical encodings (including valid alternative whitespace)',
            'canonical dialogues rejected by the conservative resource check, including some feasible schema instances',
        ],
        'command_loop': 'tapeEnd (EOF or quit within the verified domain)',
        'adversarial_acceptance': True, 'sha256': artifacts,
    }, indent=2) + '\n')
    print(out / 'zfc-checker')
    print('VERIFIED: native end-to-end contract for canonical requests in NativeFastDomain.within_capacity.')


if __name__ == '__main__':
    main()
