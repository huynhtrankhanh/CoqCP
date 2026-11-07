#!/usr/bin/env python3
"""Build and kernel-check isolated generated-code interner examples.

The fixture is not wired into the checker and does not prove general IIL
refinement or validity of the artificial collision buckets.
"""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from contextlib import nullcontext

REPO = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent


def run(*args):
    subprocess.run(list(map(str, args)), cwd=REPO, check=True)


def main():
    rocq = os.environ.get('ROCQ', 'rocq')
    build_dir = os.environ.get('UNIFORM_INTERN_FIXTURE_DIR')
    workspace = nullcontext(build_dir) if build_dir else tempfile.TemporaryDirectory(prefix='coqcp-uniform-intern-')
    with workspace as temp:
        out = Path(temp)
        out.mkdir(parents=True, exist_ok=True)
        coqcp = out / 'CoqCP'
        fixture = out / 'Fixture'
        coqcp.mkdir(exist_ok=True)
        fixture.mkdir(exist_ok=True)
        source = (REPO / 'programs/ZFCProofChecker.js').read_text()
        marker = "procedure('main'"
        if source.count(marker) != 1:
            raise RuntimeError('Cannot identify generated main')
        source = source[:source.index(marker)]
        meta = '  meta: array([int64], 32),'
        if source.count(meta) != 1:
            raise RuntimeError('Cannot identify generated environment')
        source = source.replace(meta, meta + '''
  uniformState: array([int64, int64], 1),
  uniformNodes: array([int64, int64, int64], 0),
  uniformLinks: array([int64], 0),
  uniformFormulaMap: array([int64, int64], 0),
  uniformCompiled: array([int64, int64], 0),
  uniformTemplates: array([int64], 0),
  uniformBuckets: array([int64], 1024),''')
        source += (REPO / 'programs/ZFCProofChecker/uniform-symbols.js.in').read_text()
        source += "\nprocedure('main', {}, () => { call('uniformIntern', {tag: 1, a: 2, b: 3}) })\n"
        program = fixture / 'UniformInternProgram.js'
        program.write_text(source)
        run('node', REPO / 'compiler/dist/cli.js', fixture / 'UniformInternProgram.v',
            out / 'program.cpp', program, REPO / 'programs/IO/PrintInt64.js')
        flags = ['-q', '-Q', coqcp, 'CoqCP', '-Q', fixture, 'UniformInternFixture']
        for name in ('Options', 'Imperative', 'Execution', 'InteractiveExecution'):
            dest = coqcp / (name + '.v')
            shutil.copyfile(REPO / 'theories' / dest.name, dest)
            run(rocq, 'compile', *flags, dest)
        run(rocq, 'compile', *flags, fixture / 'UniformInternProgram.v')
        model = fixture / 'UniformInternModel.v'
        shutil.copyfile(HERE.parent / 'proof' / model.name, model)
        run(rocq, 'compile', *flags, model)
        example = fixture / 'UniformInternRun.v'
        shutil.copyfile(HERE / example.name, example)
        run(rocq, 'compile', *flags, example)
        run(rocq, 'check', '-silent', '-Q', coqcp, 'CoqCP', '-Q', fixture,
            'UniformInternFixture', 'UniformInternFixture.UniformInternRun')
    print('Uniform interner concrete collision execution checked.')


if __name__ == '__main__':
    main()
