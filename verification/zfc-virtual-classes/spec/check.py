#!/usr/bin/env python3
"""Check the standalone protocol and ZFC specification without any checker implementation."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--rocq', default='/opt/rocq/9.3.0/bin/rocq')
    args = parser.parse_args()
    spec = Path(__file__).resolve().parent
    repo = spec.parents[2]
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    for directory in ['CoqCP', 'Trusted']:
        (out / directory).mkdir()
    flags = ['-q', '-Q', str(out / 'CoqCP'), 'CoqCP', '-Q', str(out / 'Trusted'), 'Trusted']

    def compile_file(path):
        subprocess.run([args.rocq, 'compile', *flags, str(path)], check=True)

    artifacts = {}
    for source, namespace in [(repo / 'theories' / f'{name}.v', 'CoqCP')
                              for name in ['Options', 'Imperative', 'Execution',
                                           'InteractiveExecution', 'DecimalEncoding']] + [
            (spec / f'{name}.v', 'Trusted') for name in
            ['SetTheory', 'VirtualClasses', 'Schemata', 'Protocol', 'Guarantees', 'Spec']]:
        target = out / namespace / source.name
        shutil.copy2(source, target)
        compile_file(target)
        artifacts[f'{namespace}/{source.name}'] = hashlib.sha256(target.read_bytes()).hexdigest()
    audited = ['Guarantees.' + name for name in re.findall(
        r'^(?:Lemma|Theorem) (\w+)', (spec / 'Guarantees.v').read_text(), re.M)]
    audited.append('Trusted.Spec.required_iff_protocol')
    audit = out / 'Audit.v'
    audit.write_text('From CoqCP Require Import Options.\n'
                     'From Trusted Require Import Spec.\n' +
                     ''.join(f'Print Assumptions {name}.\n' for name in audited))
    result = subprocess.run([args.rocq, 'compile', *flags, str(audit)],
                            text=True, capture_output=True, check=True)
    (out / 'assumptions.log').write_text(result.stdout + result.stderr)
    if result.stdout.count('Closed under the global context') != len(audited) or 'Axioms:' in result.stdout:
        raise RuntimeError('Unexpected specification assumptions')
    with (out / 'kernel.log').open('w') as log:
        subprocess.run([args.rocq, 'check', '-silent', *flags[1:], 'Trusted.Spec'],
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    (out / 'specification-status.json').write_text(json.dumps({
        'standalone_specification': 'checked', 'implementation_imports': [],
        'kernel_recheck': 'passed', 'assumption_audits': len(audited),
        'global_assumptions': [], 'native_end_to_end_refinement': 'not asserted',
        'sha256': artifacts,
    }, indent=2) + '\n')
    print(f'Standalone specification checked; {len(audited)} closed assumption audits.')


if __name__ == '__main__':
    main()
