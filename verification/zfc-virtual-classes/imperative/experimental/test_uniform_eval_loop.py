#!/usr/bin/env python3
"""Kernel-check the experimental evaluator's generated loop exit branches.

The fixture compiles the actual IIL evaluator and its helper procedures with
the production checker environment. It does not prove the complete evaluator.
"""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

REPO = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
PARTS = REPO / 'programs/ZFCProofChecker'


def run(*args):
    subprocess.run(list(map(str, args)), cwd=REPO, check=True)


def main():
    rocq = os.environ.get('ROCQ', 'rocq')
    with tempfile.TemporaryDirectory(prefix='coqcp-uniform-eval-loop-') as temp:
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
  uniformState: array([int64, int64], 1),
  uniformNodes: array([int64, int64, int64], 0),
  uniformLinks: array([int64], 0),
  uniformFormulaMap: array([int64, int64], 0),
  uniformCompiled: array([int64, int64], 0),
  uniformTemplates: array([int64], 0),
  uniformMemoState: array([int64, int64, int64, int64], 1),
  uniformMemoBuckets: array([int64], 1024),
  uniformMemoEntries: array([int64, int64, int64, int64], 0),
  uniformEvalState: array([int64], 1),
  uniformEvalStack: array([int64, int64, int64], 0),
  uniformBuckets: array([int64], 1024),''')
        for name in ('symbols', 'memo', 'eval'):
            source += (PARTS / f'uniform-{name}.js.in').read_text()
        source += "\nprocedure('main', {}, () => { call('uniformEvaluate', {root: 0}) })\n"
        program = fixture / 'EvalProgram.js'
        program.write_text(source)
        run('node', REPO / 'compiler/dist/cli.js', fixture / 'EvalProgram.v',
            out / 'program.cpp', program, REPO / 'programs/IO/PrintInt64.js')
        flags = ['-q', '-Q', coqcp, 'CoqCP', '-Q', fixture, 'UniformEvalFull']
        for name in ('Options', 'Imperative', 'Execution'):
            dest = coqcp / (name + '.v')
            shutil.copyfile(REPO / 'theories' / dest.name, dest)
            run(rocq, 'compile', *flags, dest)
        run(rocq, 'compile', *flags, fixture / 'EvalProgram.v')
        proof = fixture / 'UniformEvalLoop.v'
        shutil.copyfile(HERE / proof.name, proof)
        run(rocq, 'compile', *flags, proof)
        run(rocq, 'check', '-silent', '-Q', coqcp, 'CoqCP', '-Q', fixture,
            'UniformEvalFull', 'UniformEvalFull.UniformEvalLoop')
    print('Uniform evaluator generated loop exits checked.')


if __name__ == '__main__':
    main()
