#!/usr/bin/env python3
"""Compile the unconnected memo template and check a concrete Rocq execution.

This test uses production formulaHash, but the wrapper is only a fixture and is
not the production proofchecker. It does not establish universal refinement.
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
    with tempfile.TemporaryDirectory(prefix='coqcp-uniform-memo-') as temp:
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
        meta = '  meta: array([int64], 32),'
        if source.count(meta) != 1:
            raise RuntimeError('Cannot identify the generated program environment')
        source = source.replace(meta, meta + '''
  uniformMemoState: array([int64, int64, int64, int64], 1),
  uniformMemoBuckets: array([int64], 1024),
  uniformMemoEntries: array([int64, int64, int64, int64], 0),''')
        source += (REPO / 'programs/ZFCProofChecker/uniform-memo.js.in').read_text()
        source += "\nprocedure('main', {}, () => { call('uniformMemoReset', {}); call('uniformMemoGet', {node: 0, depth: 0}); call('uniformMemoPutNew', {node: 0, depth: 0, value: 0}) })\n"
        program = fixture / 'UniformMemoProgram.js'
        program.write_text(source)
        run('node', REPO / 'compiler/dist/cli.js', fixture / 'UniformMemoProgram.v',
            out / 'program.cpp', program, REPO / 'programs/IO/PrintInt64.js')
        flags = ['-q', '-Q', coqcp, 'CoqCP', '-Q', fixture, 'UniformMemoFixture']
        for name in ('Options', 'Imperative', 'Execution', 'InteractiveExecution'):
            dest = coqcp / (name + '.v')
            shutil.copyfile(REPO / 'theories' / dest.name, dest)
            run(rocq, 'compile', *flags, dest)
        run(rocq, 'compile', *flags, fixture / 'UniformMemoProgram.v')
        chains = fixture / 'UniformMemoChains.v'
        shutil.copyfile(HERE.parent / 'proof' / chains.name, chains)
        run(rocq, 'compile', *flags, chains)
        frame = fixture / 'ArrayLengthFrame.v'
        shutil.copyfile(HERE.parent / 'proof' / frame.name, frame)
        run(rocq, 'compile', *flags, frame)
        effects = fixture / 'EffectFrame.v'
        shutil.copyfile(HERE.parent / 'proof' / effects.name, effects)
        run(rocq, 'compile', *flags, effects)
        uniform_frame = fixture / 'UniformMemoFrame.v'
        shutil.copyfile(HERE / uniform_frame.name, uniform_frame)
        run(rocq, 'compile', *flags, uniform_frame)
        contents = fixture / 'UniformMemoContents.v'
        shutil.copyfile(HERE / contents.name, contents)
        run(rocq, 'compile', *flags, contents)
        loop = fixture / 'UniformMemoLoop.v'
        shutil.copyfile(HERE / loop.name, loop)
        run(rocq, 'compile', *flags, loop)
        prelude = fixture / 'UniformMemoPrelude.v'
        shutil.copyfile(HERE / prelude.name, prelude)
        run(rocq, 'compile', *flags, prelude)
        example = fixture / 'UniformMemoRun.v'
        shutil.copyfile(HERE / 'UniformMemoRun.v', example)
        run(rocq, 'compile', *flags, example)
        run(rocq, 'check', '-silent', '-Q', coqcp, 'CoqCP', '-Q', fixture,
            'UniformMemoFixture', 'UniformMemoFixture.UniformMemoRun',
            'UniformMemoFixture.UniformMemoFrame', 'UniformMemoFixture.UniformMemoContents',
            'UniformMemoFixture.UniformMemoLoop', 'UniformMemoFixture.UniformMemoPrelude')
    print('Uniform memo generated-code execution and refinement instances checked.')


if __name__ == '__main__':
    main()
