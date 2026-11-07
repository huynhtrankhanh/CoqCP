#!/usr/bin/env python3
"""Exercise the unproved uniform-schema design through a real IIL dialogue.

This constructs and compiles an isolated temporary checker. It does not modify
the production generator or establish refinement of the Rocq specification.
The wrapper caches by immutable proof-root ID. Its resource handling and I/O
are tested only by the examples below; this harness does not prove the
protocol's full acceptance and rejection behavior.
"""
import select
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
PARTS = ROOT / 'programs/ZFCProofChecker'


def experimental_source():
    source = (ROOT / 'programs/ZFCProofChecker.js').read_text()
    source = source.replace('environment({', '''environment({
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
  uniformBuckets: array([int64], 1024),
  uniformRoots: array([int64, int64], 0),''', 1)
    binding = "call('bindName', { value: get('a'), kind: 2 })"
    assert source.count(binding) == 1
    source = source.replace(binding, '''call('lookup', {})
      if (retrieve('meta', 0)[0] != 18446744073709551615) { call('no', {}) } else {
        call('uniformCompile', {root: get('a')})
        if (retrieve('meta', 8)[0] == 0) {
          if (retrieve('meta', 18)[0] == 0) { call('no', {}) } else {
            grow('uniformRoots', get('a') + 1)
            store('uniformRoots', get('a'), [retrieve('meta', 0)[0], 1])
            call('bindName', {value: get('a'), kind: 2})
          }
        }
      }''')
    instance = "call('schemaInstance', { root: get('node') })"
    assert source.count(instance) == 1
    source = source.replace(instance, '''if (retrieve('uniformRoots', get('node'))[1] == 0) {
      store('meta', 8, [1])
    } else {
      call('uniformEvaluate', {root: retrieve('uniformRoots', get('node'))[0]})
    }''')
    marker = "procedure(\n  'command',"
    assert source.count(marker) == 1
    code = '\n'.join((PARTS / f'uniform-{name}.js.in').read_text()
                     for name in ('symbols', 'memo', 'eval'))
    return source.replace(marker, code + '\n' + marker)


class Client:
    def __init__(self, binary):
        self.process = subprocess.Popen([str(binary)], text=True, stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.expect_line('SEED')
        self.expect('506097522914230528 1084818905618843912', 'READY')

    def line(self):
        if not select.select([self.process.stdout], [], [], 5)[0]:
            raise AssertionError('checker did not flush a reply')
        return self.process.stdout.readline().strip()

    def expect_line(self, expected):
        actual = self.line()
        if actual != expected:
            raise AssertionError(f'expected {expected!r}, got {actual!r}')

    def send(self, command):
        self.process.stdin.write(command + '\n')
        self.process.stdin.flush()
        return self.line()

    def expect(self, command, expected):
        actual = self.send(command)
        if actual != expected:
            raise AssertionError(f'{command}: expected {expected!r}, got {actual!r}')

    def ok(self, command):
        result = self.send(command)
        if not result.startswith('OK '):
            raise AssertionError(f'{command}: expected OK, got {result!r}')
        return int(result[3:])

    def node(self, kind, a=0, b=0, c=0, d=0):
        return self.ok(f'22 {kind} {a} {b} {c} {d}')

    def close(self):
        self.process.stdin.close()
        self.process.wait(timeout=5)
        error = self.process.stderr.read()
        self.process.stdout.close()
        self.process.stderr.close()
        if self.process.returncode:
            raise AssertionError(error)


def test_dialogue(binary):
    c = Client(binary)
    try:
        c.expect('25 missing', 'NO')
        c.expect('26 missing', 'NO')
        # A class-metavariable identity proof, generalized over one set.
        meta = c.node(0, 0)
        literal = c.node(1, c.ok('5 0'))
        p = c.node(5, literal, meta)
        pp = c.node(6, p, p)
        k1 = c.node(8, 0, p, p)
        k2 = c.node(8, 0, p, pp)
        s = c.node(8, 1, p, pp, p)
        first = c.node(9, s, k2)
        root = c.node(10, c.node(9, first, k1))
        assert c.ok(f'23 {root} identity') == root
        c.expect('25 identity', 'SCHEMA')
        assert c.ok('26 identity') == 1
        c.expect(f'23 {root} identity', 'NO')
        c.expect(f'23 {meta} wrongtype', 'NO')
        assert c.ok(f'23 {root} alias') == root
        assert c.ok('26 alias') == 1

        cls = c.ok('5 5')
        body = c.ok('2 0 1')
        abstraction = c.ok(f'6 {body}')
        for argument, atom in ((cls, c.ok('2 0 6')), (abstraction, body)):
            atom_imp = c.ok(f'3 {atom} {atom}')
            expected = c.ok(f'4 {atom_imp}')
            theorem = c.ok(f'24 identity 1 {argument}')
            assert c.ok(f'19 {theorem}') == expected
        c.expect('24 identity 0', 'NO')
        c.expect(f'24 identity 2 {cls} {cls}', 'NO')
        c.expect('24 identity 1 9999999', 'NO')
        c.expect(f'24 missing 1 {cls}', 'NO')
        alias_theorem = c.ok(f'24 alias 1 {abstraction}')
        assert c.ok(f'19 {alias_theorem}') == expected

        # Reuse the same proof with two surrounding binders. Both set and
        # abstract class arguments must shift their free variables correctly.
        twice = c.node(10, root)
        assert c.ok(f'23 {twice} twice') == twice
        for argument, atom in ((cls, c.ok('2 0 7')),
                               (abstraction, c.ok('2 0 2'))):
            implication = c.ok(f'3 {atom} {atom}')
            one_all = c.ok(f'4 {implication}')
            two_all = c.ok(f'4 {one_all}')
            twice_theorem = c.ok(f'24 twice 1 {argument}')
            assert c.ok(f'19 {twice_theorem}') == two_all

        # This MP succeeds for X=Y=0 but is not valid for every substitution.
        other = c.node(0, 1)
        phi = c.node(4, meta, other)
        zero = c.ok('1 0 0')
        psi = c.node(2, zero)
        imp = c.node(8, 0, phi, psi)
        refl = c.node(8, 5, 0)
        nonuniform = c.node(9, imp, refl)
        c.expect(f'23 {nonuniform} nonuniform', 'NO')
        c.expect('25 nonuniform', 'NO')
        c.expect('24 nonuniform 2 0 0', 'NO')

        # A saved implication must be normalized to permit symbolic MP.
        zero_refl = c.ok('11 5 0 0 0')
        saved_k = c.ok(f'11 0 {zero} {zero} 0')
        saved_k_node = c.node(11, saved_k)
        saved_refl_node = c.node(11, zero_refl)
        saved_root = c.node(9, saved_k_node, saved_refl_node)
        assert c.ok(f'23 {saved_root} saved_mp') == saved_root
        assert c.ok('26 saved_mp') == 0
        saved_instance = c.ok('24 saved_mp 0')
        assert c.ok(f'19 {saved_instance}') == c.ok(f'3 {zero} {zero}')

        # Unrelated class/theorem naming and history operations still work.
        assert c.ok(f'9 {cls} namedclass') == cls
        c.expect('25 namedclass', 'CLASS')
        assert c.ok('10 namedclass') == cls
        c.expect(f'23 {root} namedclass', 'NO')
        c.expect(f'9 {cls} identity', 'NO')
        theorem = c.ok('11 5 7 0 0')
        formula = c.ok(f'19 {theorem}')
        assert c.ok(f'20 {theorem} saved') == formula
        c.expect('25 saved', 'THEOREM')
        c.ok('17')
        recalled = c.ok('21 saved')
        assert c.ok(f'19 {recalled}') == formula
        after_reset = c.ok(f'24 identity 1 {abstraction}')
        assert c.ok(f'19 {after_reset}') == expected
        c.expect('0', 'BYE')
    finally:
        c.close()

    # Malformed numeric input terminates a session with ERR; each test uses a
    # fresh session because a fatal parse error ends the protocol loop.
    for request in ('23 not-a-number bad', '24 missing 2 0 not-a-number'):
        c = Client(binary)
        try:
            c.expect(request, 'ERR')
        finally:
            c.close()


def main():
    with tempfile.TemporaryDirectory(prefix='coqcp-uniform-dialogue-') as temp:
        out = Path(temp)
        source = out / 'UniformDialogue.js'
        source.write_text(experimental_source())
        subprocess.run(['node', str(ROOT / 'compiler/dist/cli.js'), str(out / 'program.v'),
                        str(out / 'program.cpp'), str(source), str(ROOT / 'programs/IO/PrintInt64.js')],
                       cwd=ROOT, check=True)
        subprocess.run(['g++', '-std=c++20', '-O2', '-w', str(out / 'program.cpp'),
                        '-o', str(out / 'checker')], cwd=ROOT, check=True)
        test_dialogue(out / 'checker')
    print('uniform experimental dialogue: PASS')


if __name__ == '__main__':
    main()
