#!/usr/bin/env python3
"""Build CoqCP source to native C++ and independently recheck generated Rocq.

This is a development build. Main's execution refinement is not implied by typechecking its generated definition.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--rocq', default='/opt/rocq/9.3.0/bin/rocq')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    repo = here.parents[2]
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    code = out / 'Code'
    code.mkdir()
    proofs = out / 'Proof'
    proofs.mkdir()

    def run(command):
        subprocess.run(list(map(str, command)), cwd=repo, check=True)

    run([sys.executable, repo / 'programs/ZFCProofChecker/generate.py'])
    shutil.copy2(repo / 'programs/ZFCProofChecker.js', out / 'ProofChecker.js')
    run(['node', repo / 'compiler/dist/cli.js', code / 'ProofChecker.v',
         out / 'checker.cpp', out / 'ProofChecker.js', repo / 'programs/IO/PrintInt64.js'])
    (out / 'CoqCP').mkdir()
    (out / 'Trusted').mkdir()
    flags = ['-q', '-Q', str(out / 'CoqCP'), 'CoqCP', '-Q', str(code), 'ImperativeZFC',
             '-Q', str(proofs), 'NativeProof', '-Q', str(out / 'Trusted'), 'Trusted']
    for name in ['Options', 'Imperative', 'Execution', 'TapeEnd', 'InteractiveExecution', 'DecimalEncoding']:
        source = out / 'CoqCP' / f'{name}.v'
        origin = repo / 'theories' / source.name
        shutil.copy2(origin, source)
        run([args.rocq, 'compile', *flags, source])
    for name in ['SetTheory', 'VirtualClasses', 'Schemata', 'Protocol', 'Spec']:
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
    proof_modules = ['Index', 'Overflow', 'Lift', 'ArrayFacts', 'SipHash', 'HashScan', 'InternTail', 'HashTable',
                     'Stack', 'PrintingFrame', 'SipHashVector']
    for name in proof_modules:
        source = proofs / f'{name}.v'
        shutil.copy2(here / 'proof' / source.name, source)
        run([args.rocq, 'compile', *flags, source])
    audited = ['funcdef_0__main', 'tapeEnd_execution',
               'IndexExecution.index_execution', 'OverflowExecution.overflow_rejected',
               'IndexSemantics.generated_index_correct', 'IndexSemantics.generated_checked_index',
               'StackExecution.generated_checked_push', 'PrintingFrame.generated_ok_preserves',
               'SipHashVector.official_vector_24',
               'SipHashExecution.generated_round', 'SipHashExecution.generated_word',
               'SipHashExecution.generated_hash_correct',
               'HashScanExecution.scan_loop_checked', 'HashScanExecution.scan_loop_complete',
               'InternTailExecution.after_scan_found', 'InternTailExecution.after_scan_full',
               'InternTailExecution.after_scan_fresh', 'InternTailExecution.append_table_valid',
               'HashTableInvariant.append_indexed', 'HashTableInvariant.scan_miss_absent']
    (code / 'Audit.v').write_text(
        'From CoqCP Require Import Options TapeEnd.\n'
        'From ImperativeZFC Require Import ProofChecker.\n'
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
                        'CoqCP.TapeEnd', 'ImperativeZFC.NativeContract', 'NativeProof.Lift',
                        'NativeProof.Stack', 'NativeProof.PrintingFrame', 'NativeProof.SipHashVector',
                        'NativeProof.SipHash', 'NativeProof.HashScan',
                        'NativeProof.InternTail', 'NativeProof.HashTable'],
                       cwd=repo, check=True, stdout=log, stderr=subprocess.STDOUT)
    with (out / 'cpp-build.log').open('w') as log:
        subprocess.run(['g++', '-std=c++20', '-O2', str(out / 'checker.cpp'),
                        '-o', str(out / 'zfc-checker')], check=True,
                       stdout=log, stderr=subprocess.STDOUT)
    artifacts = {name: hashlib.sha256((out / name).read_bytes()).hexdigest()
                 for name in ['ProofChecker.js', 'Code/ProofChecker.v', 'checker.cpp', 'zfc-checker']
                 + [f'Proof/{name}.v' for name in proof_modules]}
    (out / 'development-status.json').write_text(json.dumps({
        'status': 'incomplete', 'implementation': 'CoqCP imperative DSL to C++',
        'generated_rocq_kernel_recheck': 'passed', 'main_global_assumptions': [],
        'proved_generated_execution': [
            'checked index substitution and overflow rejection',
            'explicit traversal stack push',
            'formatter memory preservation',
            'tapeEnd finite-input semantics',
            'SipHash-2-4 published 24-byte test vector',
            'general SipHash-2-4 execution, digest, bucket bounds and memory preservation',
            'collision-chain scan termination, exact matches, and reachable-entry completeness',
            'generated interner insertion branch, immutable earlier IDs and descending links',
            'bucket reachability preserved by insertion; misses imply freshness without hash injectivity',
        ],
        'command_loop': 'tapeEnd (EOF, quit, or fatal error)',
        'missing_obligations': ['generated-main end-to-end execution refinement',
                                'native hash-table rehashing and full interner composition/representation invariants',
                                'native schema evaluator refinement'],
        'adversarial_acceptance': False, 'sha256': artifacts,
    }, indent=2) + '\n')
    print(out / 'zfc-checker')
    print('INCOMPLETE: generated definition rechecked; native end-to-end refinement remains open.')


if __name__ == '__main__':
    main()
