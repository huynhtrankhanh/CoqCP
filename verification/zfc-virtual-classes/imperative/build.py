#!/usr/bin/env python3
"""Build CoqCP source to native C++ and independently recheck generated Rocq.

This is a development build. Neither main's refinement nor unconditional ZFC
consistency is claimed by successfully typechecking its generated definition.
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

    run([sys.executable, here / 'generate.py'])
    shutil.copy2(here / 'ProofChecker.js', out / 'ProofChecker.js')
    run(['node', repo / 'compiler/dist/cli.js', code / 'ProofChecker.v',
         out / 'checker.cpp', out / 'ProofChecker.js', repo / 'programs/IO/PrintInt64.js'])
    (out / 'CoqCP').mkdir()
    flags = ['-q', '-Q', str(out / 'CoqCP'), 'CoqCP', '-Q', str(code), 'ImperativeZFC',
             '-Q', str(proofs), 'NativeProof']
    for name in ['Options', 'Imperative', 'Execution', 'TapeEnd', 'SetTheory']:
        source = out / 'CoqCP' / f'{name}.v'
        shutil.copy2(repo / 'theories' / source.name, source)
        run([args.rocq, 'compile', *flags, source])
    run([args.rocq, 'compile', *flags, code / 'ProofChecker.v'])
    proof_modules = ['Index', 'Overflow', 'Lift', 'Intern', 'Fresh',
                     'Representation', 'Canonical', 'Stack', 'PrintingFrame',
                     'Append', 'Inference', 'ModusPonens', 'InternFrame', 'Generalization', 'State']
    for name in proof_modules:
        source = proofs / f'{name}.v'
        shutil.copy2(here / 'proof' / source.name, source)
        run([args.rocq, 'compile', *flags, source])
    audited = [
        'funcdef_0__main',
        'step_input_length',
        'execLocal_input_length',
        'tape_loop_sound',
        'tape_loop_complete',
        'tapeEnd_execution',
        'IndexExecution.index_execution',
        'OverflowExecution.overflow_rejected',
        'IndexSemantics.generated_index_correct',
        'IndexSemantics.generated_checked_index',
        'InternExecution.intern_existing',
        'FreshExecution.generated_intern_correct',
        'FreshExecution.fresh_formulas',
        'FreshExecution.fresh_metadata',
        'NativeRepresentation.generated_intern_history',
        'NativeRepresentation.intern_output_ready',
        'CanonicalArena.decode_injective',
        'CanonicalArena.generated_intern_canonical',
        'StackExecution.generated_checked_push',
        'StackExecution.push_preserves_previous',
        'PrintingFrame.translated_print_preserves',
        'PrintingFrame.generated_ok_preserves',
        'AppendExecution.generated_append_fits',
        'AppendExecution.generated_append_safe',
        'AppendExecution.generated_append_fits_post',
        'NativeInference.append_modus_ponens',
        'NativeInference.append_generalization',
        'NativeInference.append_axiom',
        'CanonicalArena.formula_id_equality',
        'CanonicalArena.decode_implication',
        'ModusPonensExecution.generated_no_preserves',
        'ModusPonensExecution.generated_mp_branch',
        'ModusPonensExecution.generated_modus_ponens_safe',
        'ModusPonensExecution.generated_modus_ponens_accepts',
        'InternFrame.intern_output_frame',
        'InternFrame.intern_output_history_ready',
        'InternFrame.intern_output_failed',
        'GeneralizationExecution.generated_generalize_step',
        'GeneralizationExecution.generated_append_formula_frame',
        'GeneralizationExecution.generated_generalization_safe',
        'GeneralizationExecution.generated_generalization_post',
        'NativeState.represented_formula_unique',
        'NativeState.represents_unique',
        'NativeState.append_post_ready',
        'NativeState.append_post_history_ready',
        'NativeState.append_post_canonical',
        'NativeState.append_post_words',
        'NativeState.generated_append_accepted',
        'NativeState.generated_append_session',
        'NativeState.generated_intern_session',
        'NativeState.generated_generalization_session',
        'NativeState.session_memory_frame',
        'NativeState.generated_modus_ponens_session',
    ]
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
                        'CoqCP.TapeEnd', 'ImperativeZFC.ProofChecker', 'NativeProof.Lift',
                        'NativeProof.Stack', 'NativeProof.ModusPonens',
                        'NativeProof.Generalization', 'NativeProof.State'],
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
            'total index substitution in all seven modes with mandatory overflow rejection',
            'de Bruijn renaming under binders and preservation of other arrays and I/O',
            'formula interning: first existing node, fresh append, or full-arena rejection',
            'formula denotations and theorem history preserved by native interning',
            'canonical formula IDs preserved by native interning',
            'explicit traversal-stack push with counter overflow rejection and frame preservation',
            'native OK formatter preserves every array except its print buffer',
            'native theorem append preserves derivability and implements exact history updates',
            'native append is sound for axiom, modus ponens, and generalization ID conditions',
            'native modus ponens executes sound append or rejection and recognizes canonical matches',
            'native generalization preserves derivability and appends the quantified source theorem',
            'native interning, append, and generalization preserve the composed session invariants',
            'native modus ponens preserves the composed session invariants on acceptance and rejection',
            'tapeEnd finite-input execution equals an EOF-or-break relation without numeric fuel',
        ],
        'maximum_command_iterations': str(2**256),
        'missing_obligations': ['generated-main execution refinement', 'SetTheory.consistent'],
        'adversarial_acceptance': False, 'sha256': artifacts,
    }, indent=2) + '\n')
    print(out / 'zfc-checker')
    print('INCOMPLETE: generated definition rechecked; main refinement and Con(ZFC) unproved.')


if __name__ == '__main__':
    main()
