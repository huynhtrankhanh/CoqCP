#!/usr/bin/env python3
"""Kernel-check the experimental evaluator's generated stack-push action.

The fixture compiles the exact IIL procedure with the production checker
environment. It does not establish correctness of the complete evaluator.
"""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

REPO = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent


def run(*args):
    subprocess.run(list(map(str, args)), cwd=REPO, check=True)


def main():
    rocq = os.environ.get('ROCQ', 'rocq')
    with tempfile.TemporaryDirectory(prefix='coqcp-uniform-eval-push-') as temp:
        out = Path(temp)
        coqcp = out / 'CoqCP'
        fixture = out / 'Fixture'
        coqcp.mkdir()
        fixture.mkdir()
        source = (REPO / 'programs/ZFCProofChecker.js').read_text()
        marker = "procedure('main'"
        if source.count(marker) != 1:
            raise RuntimeError('Cannot identify the generated program main')
        source = source[:source.index(marker)]
        environment = '  meta: array([int64], 32),'
        if source.count(environment) != 1:
            raise RuntimeError('Cannot identify the generated program environment')
        source = source.replace(environment, environment + '''
  uniformEvalState: array([int64], 1),
  uniformEvalStack: array([int64, int64, int64], 0),''')
        template = (REPO / 'programs/ZFCProofChecker/uniform-eval.js.in').read_text()
        delimiter = '// This traversal'
        if template.count(delimiter) != 1:
            raise RuntimeError('Cannot identify the experimental push procedure')
        source += template[:template.index(delimiter)]
        source += "\nprocedure('main', {}, () => { call('uniformEvalPush', {node: 0, depth: 0}) })\n"
        program = fixture / 'UniformEvalProgram.js'
        program.write_text(source)
        run('node', REPO / 'compiler/dist/cli.js', fixture / 'UniformEvalProgram.v',
            out / 'program.cpp', program, REPO / 'programs/IO/PrintInt64.js')
        flags = ['-q', '-Q', coqcp, 'CoqCP', '-Q', fixture, 'UniformEvalFixture']
        for name in ('Options', 'Imperative', 'Execution'):
            dest = coqcp / (name + '.v')
            shutil.copyfile(REPO / 'theories' / dest.name, dest)
            run(rocq, 'compile', *flags, dest)
        run(rocq, 'compile', *flags, fixture / 'UniformEvalProgram.v')
        proof = fixture / 'UniformEvalPush.v'
        shutil.copyfile(HERE / proof.name, proof)
        run(rocq, 'compile', *flags, proof)
        run(rocq, 'check', '-silent', '-Q', coqcp, 'CoqCP', '-Q', fixture,
            'UniformEvalFixture', 'UniformEvalFixture.UniformEvalPush')
    print('Uniform evaluator generated stack-push action checked.')


if __name__ == '__main__':
    main()
