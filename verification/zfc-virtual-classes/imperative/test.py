#!/usr/bin/env python3
"""Differential native tests against the separate Gallina reference checker."""
import argparse
import select
import subprocess
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from test_checker import parse_formula
from test_siphash import siphash

BINARY = REFERENCE = None
MAX = 2**64 - 1
SEED = '506097522914230528 1084818905618843912\n'


class Client:
    def __init__(self):
        self.process = subprocess.Popen([str(BINARY)], text=True, stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.formulas = {'false': 0}
        if not select.select([self.process.stdout], [], [], 5)[0]:
            raise AssertionError('Missing seed prompt')
        if self.process.stdout.readline().strip() != 'SEED':
            raise AssertionError('Expected SEED')
        if self.send(SEED.strip()) != 'READY':
            raise AssertionError('Seed rejected')

    def send(self, command):
        self.process.stdin.write(str(command) + '\n')
        self.process.stdin.flush()
        if not select.select([self.process.stdout], [], [], 5)[0]:
            raise AssertionError('No flushed response: ' + str(command))
        return self.process.stdout.readline().strip()

    def ok(self, command):
        response = self.send(command)
        if not response.startswith('OK '):
            raise AssertionError(f'{command}: expected OK, got {response}')
        return int(response[3:])

    def formula(self, p):
        key = str(p)
        if key in self.formulas:
            return self.formulas[key]
        op, *args = p
        if op in ['=', 'in']:
            index = self.ok(f'{1 if op == "=" else 2} {args[0]} {args[1]}')
        elif op == 'imp':
            a, b = map(self.formula, args)
            index = self.ok(f'3 {a} {b}')
        elif op == 'all':
            index = self.ok(f'4 {self.formula(args[0])}')
        else:
            raise AssertionError(p)
        self.formulas[key] = index
        return index

    def close(self):
        if self.process.poll() is None:
            self.process.stdin.close()
            self.process.wait(timeout=5)
        error = self.process.stderr.read()
        for stream in [self.process.stdin, self.process.stdout, self.process.stderr]:
            stream.close()
        if self.process.returncode != 0:
            raise AssertionError(error)


def reference(command):
    result = subprocess.run([str(REFERENCE)], input=command + '\n', text=True,
                            capture_output=True, timeout=5, check=True)
    return result.stdout.splitlines()


def serialize(p):
    return p if isinstance(p, str) else '(' + ' '.join(map(serialize, p)) + ')'


def neg(p): return ['imp', p, 'false']
def conj(p, q): return neg(['imp', p, neg(q)])


class NativeTests(unittest.TestCase):
    def setUp(self):
        self.c = Client()

    def tearDown(self):
        self.c.close()

    def schema(self, kind, a=0, b=0, c=0, d=0):
        return self.c.ok(f'22 {kind} {a} {b} {c} {d}')

    def identity_schema(self, generalize=True):
        # An unrelated, unreachable metavariable must not affect this schema.
        self.schema(0, 999)
        meta = self.schema(0, 0)
        variable = self.schema(1, self.c.ok('5 0'))
        p = self.schema(5, variable, meta)
        pp = self.schema(6, p, p)
        k1 = self.schema(8, 0, p, p)
        k2 = self.schema(8, 0, p, pp)
        s = self.schema(8, 1, p, pp, p)
        first = self.schema(9, s, k2)
        root = self.schema(9, first, k1)
        return self.schema(10, root) if generalize else root

    def test_named_theorem_snapshot_survives_undo_reset_and_reuse(self):
        self.c.ok('11 5 7 0 0')
        expected = self.c.formula(['=', '7', '7'])
        self.assertEqual(self.c.ok('20 0 reflexive'), expected)
        self.assertEqual(self.c.send('25 reflexive'), 'THEOREM')
        self.c.ok('17')
        self.c.ok('11 5 8 0 0')
        recalled = self.c.ok('21 reflexive')
        self.assertEqual(self.c.ok(f'19 {recalled}'), expected)
        cls = self.c.ok('5 0')
        self.assertEqual(self.c.send(f'9 {cls} reflexive'), 'NO')
        self.assertEqual(self.c.send('10 reflexive'), 'NO')
        self.assertEqual(self.c.send('15 reflexive'), 'NO')
        self.assertEqual(self.c.send('14 reflexive 0'), 'NO')
        self.assertEqual(self.c.send('21 missing'), 'NO')

    def test_class_metavariable_identity_schema_and_binder_capture(self):
        root = self.identity_schema()
        self.c.ok(f'23 {root} identity')
        self.assertEqual(self.c.send('25 identity'), 'SCHEMA')
        self.assertEqual(self.c.ok('26 identity'), 1)
        for cls, atom in [
            (self.c.ok('5 5'), ['in', '0', '6']),
            (self.c.ok(f"6 {self.c.formula(['in', '0', '1'])}"), ['in', '0', '1']),
        ]:
            theorem = self.c.ok(f'24 identity 1 {cls}')
            self.assertEqual(self.c.ok(f'19 {theorem}'), self.c.formula(['all', ['imp', atom, atom]]))
        self.c.ok('17')
        theorem = self.c.ok(f'24 identity 1 {cls}')
        self.assertEqual(theorem, 0)
        self.assertEqual(self.c.ok('19 0'), self.c.formula(['all', ['imp', atom, atom]]))

    def test_schema_rejection_is_atomic_and_consumes_arguments(self):
        root = self.identity_schema(False)
        self.c.ok(f'23 {root} identity')
        cls = self.c.ok('5 0')
        self.assertEqual(self.c.send(f'24 identity 2 {cls} {cls}'), 'NO')
        self.assertEqual(self.c.send('24 identity 0'), 'NO')
        self.assertEqual(self.c.send('24 identity 1 9999999'), 'NO')
        self.assertEqual(self.c.send(f'24 missing 1 {cls}'), 'NO')
        ax = self.schema(8, 5, 0)
        invalid = self.schema(9, ax, ax)
        self.c.ok(f'23 {invalid} invalid')
        self.assertEqual(self.c.send('24 invalid 0'), 'NO')
        self.assertEqual(self.c.send('19 0'), 'NO')
        self.assertEqual(self.c.ok(f'24 identity 1 {cls}'), 0)

    def test_schema_node_types_and_snapshot_certificates(self):
        self.assertEqual(self.c.send('22 3 999 0 0 0'), 'NO')
        self.assertEqual(self.c.send('22 0 18446744073709551615 0 0 0'), 'NO')
        f = self.schema(2, 0)
        self.assertEqual(self.c.send(f'23 {f} formula'), 'NO')
        self.assertEqual(self.c.send(f'22 5 {f} {f} 0 0'), 'NO')
        self.c.ok('11 5 9 0 0')
        proof = self.schema(11, 0)
        self.c.ok(f'23 {proof} snapshot')
        self.c.ok('17')
        self.c.ok('11 5 10 0 0')
        result = self.c.ok('24 snapshot 0')
        self.assertEqual(self.c.ok(f'19 {result}'), self.c.formula(['=', '9', '9']))

    def test_every_axiom_matches_reference(self):
        # The reference is a separate, Rocq-proved implementation. Compare full
        # syntax via canonical arena IDs, not just truth in selected structures.
        p = ['all', ['imp', ['in', '1', '2'], ['=', '0', '3']]]
        q = ['in', '7', '0']
        r = ['=', '3', '3']
        pi, qi, ri = map(self.c.formula, [p, q, r])
        witnesses = [
            (f'(k {serialize(p)} {serialize(q)})', pi, qi, 0),
            (f'(s {serialize(p)} {serialize(q)} {serialize(r)})', pi, qi, ri),
            (f'(dne {serialize(p)})', pi, 0, 0),
            (f'(inst {serialize(p)} 5)', pi, 5, 0),
            (f'(dist {serialize(p)} {serialize(q)})', pi, qi, 0),
            ('(refl 9)', 9, 0, 0), ('(mem-left 7 8 9)', 7, 8, 9),
            ('(mem-right 7 8 9)', 7, 8, 9), ('(eq-trans 7 8 9)', 7, 8, 9),
            ('ext', 0, 0, 0), ('found', 0, 0, 0), ('pair', 0, 0, 0),
            ('union', 0, 0, 0), ('power', 0, 0, 0), ('infinity', 0, 0, 0),
            (f'(sep {serialize(p)})', pi, 0, 0),
            (f'(repl {serialize(p)})', pi, 0, 0), ('choice', 0, 0, 0),
        ]
        for tag, (witness, a, b, c) in enumerate(witnesses):
            with self.subTest(tag=tag):
                expanded = reference(f'(axiom {witness})\nshow')[1].split(' ', 1)[1]
                expected = self.c.formula(parse_formula(expanded))
                proof = self.c.ok(f'11 {tag} {a} {b} {c}')
                self.assertEqual(self.c.ok(f'19 {proof}'), expected)

    def test_modus_ponens_and_generalization(self):
        refl = self.c.ok('11 5 0 0 0')
        p = self.c.formula(['=', '0', '0'])
        k = self.c.ok(f'11 0 {p} 0 0')
        mp = self.c.ok(f'12 {k} {refl}')
        self.assertEqual(self.c.ok(f'19 {mp}'), self.c.formula(['imp', 'false', ['=', '0', '0']]))
        gen = self.c.ok(f'13 {mp}')
        self.assertEqual(self.c.ok(f'19 {gen}'), self.c.formula(['all', ['imp', 'false', ['=', '0', '0']]]))
        self.assertEqual(self.c.send(f'12 {refl} {refl}'), 'NO')
        self.assertEqual(self.c.send(f'12 {k} {k}'), 'NO')
        self.assertEqual(self.c.send(f'18 {refl} 0'), 'NO')
        self.assertEqual(self.c.send('19 999999'), 'NO')
        self.c.ok('16')
        self.assertEqual(self.c.send(f'19 {gen}'), 'NO')
        self.c.ok('17')
        self.assertEqual(self.c.send('16'), 'NO')

    def test_modus_ponens_after_history_slot_reuse(self):
        p = ['=', '0', '0']
        refl = self.c.ok('11 5 0 0 0')
        k = self.c.ok(f'11 0 {self.c.formula(p)} 0 0')
        self.assertEqual(self.c.ok('11 5 1 0 0'), 2)
        self.c.ok('16')
        self.assertEqual(self.c.send(f'12 {k} {k}'), 'NO')
        self.assertEqual(self.c.ok(f'12 {k} {refl}'), 2)
        self.assertEqual(self.c.ok('19 2'), self.c.formula(['imp', 'false', p]))
        self.c.ok('17')
        self.assertEqual(self.c.send(f'12 {k} {refl}'), 'NO')
        q = ['=', '7', '7']
        self.assertEqual(self.c.ok('11 5 7 0 0'), 0)
        self.assertEqual(self.c.ok(f'11 0 {self.c.formula(q)} 0 0'), 1)
        self.assertEqual(self.c.ok('12 1 0'), 2)
        self.assertEqual(self.c.ok('19 2'), self.c.formula(['imp', 'false', q]))

    def test_generalization_deduplication_and_history_reuse(self):
        p = ['=', '3', '3']
        refl = self.c.ok('11 5 3 0 0')
        expected = self.c.formula(['all', p])
        first = self.c.ok(f'13 {refl}')
        second = self.c.ok(f'13 {refl}')
        self.assertEqual(self.c.ok(f'19 {first}'), expected)
        self.assertEqual(self.c.ok(f'19 {second}'), expected)
        self.c.ok('16')
        nested = self.c.ok(f'13 {first}')
        self.assertEqual(nested, second)
        self.assertEqual(self.c.ok(f'19 {nested}'), self.c.formula(['all', ['all', p]]))
        self.c.ok('17')
        self.assertEqual(self.c.send(f'13 {first}'), 'NO')
        q = ['=', '8', '8']
        self.assertEqual(self.c.ok('11 5 8 0 0'), 0)
        self.assertEqual(self.c.ok('13 0'), 1)
        self.assertEqual(self.c.ok('19 1'), self.c.formula(['all', q]))

    def test_classes_match_reference_capture_and_nested_expansion(self):
        body = ['all', ['in', '1', '2']]
        abstraction = self.c.ok(f'6 {self.c.formula(body)}')
        variable = self.c.ok('5 5')
        member = self.c.ok(f'8 {variable} {abstraction}')
        expected = parse_formula(reference('(expand (class-in (set 5) (class (all (in 1 2)))))')[0])
        self.assertEqual(member, self.c.formula(expected))
        for op, text in [(7, 'class='), (8, 'class-in')]:
            result = self.c.ok(f'{op} {abstraction} {abstraction}')
            expected = parse_formula(reference(f'(expand ({text} (class {serialize(body)}) (class {serialize(body)})))')[0])
            self.assertEqual(result, self.c.formula(expected))
        nested = self.c.ok(f'6 {member}')
        result = self.c.ok(f'8 {variable} {nested}')
        expected = parse_formula(reference('(expand (class-in (set 5) (class (class-in (set 5) (class (all (in 1 2)))))))')[0])
        self.assertEqual(result, self.c.formula(expected))

    def test_name_class_and_certify_a_set_by_separation(self):
        p = ['=', '0', '0']
        body = conj(['in', '0', '1'], p)
        cls = self.c.ok(f'6 {self.c.formula(body)}')
        self.assertEqual(self.c.ok(f'9 {cls} bounded'), cls)
        self.assertEqual(self.c.send('15 bounded'), 'CLASS')
        proof = self.c.ok(f'11 15 {self.c.formula(p)} 0 0')
        self.assertEqual(self.c.ok(f'14 bounded {proof}'), cls)
        self.assertEqual(self.c.send('15 bounded'), 'SET')
        self.assertEqual(self.c.send(f'9 {cls} bounded'), 'NO')
        self.c.ok('17')
        self.assertEqual(self.c.send('15 bounded'), 'SET')
        self.assertEqual(self.c.ok('10 bounded'), cls)
        universe = self.c.ok(f'6 {self.c.formula(p)}')
        self.c.ok(f'9 {universe} universe')
        refl = self.c.ok('11 5 0 0 0')
        self.assertEqual(self.c.send(f'14 universe {refl}'), 'NO')
        self.assertEqual(self.c.send('15 universe'), 'CLASS')

    def test_set_variable_existence_via_checked_inference(self):
        i = 5
        cls = self.c.ok(f'5 {i}')
        self.c.ok(f'9 {cls} x')
        e = ['=', '0', str(i + 1)]
        a, b = ['all', neg(e)], ['=', str(i), str(i)]
        ai, bi = map(self.c.formula, [a, b])
        inst = self.c.ok(f'11 3 {self.c.formula(neg(e))} {i} 0')
        s = self.c.ok(f'11 1 {ai} {bi} 0')
        first = self.c.ok(f'12 {s} {inst}')
        k = self.c.ok(f'11 0 {bi} {ai} 0')
        refl = self.c.ok(f'11 5 {i} 0 0')
        second = self.c.ok(f'12 {k} {refl}')
        proof = self.c.ok(f'12 {first} {second}')
        self.c.ok(f'14 x {proof}')
        self.assertEqual(self.c.send('15 x'), 'SET')

    def test_machine_index_boundary(self):
        p = self.c.formula(['=', str(MAX), str(MAX)])
        proof = self.c.ok(f'11 5 {MAX} 0 0')
        self.assertEqual(self.c.ok(f'19 {proof}'), p)
        # A shift at the boundary must fail closed instead of wrapping to zero.
        self.assertEqual(self.c.send(f'11 4 {p} 0 0'), 'ERR')

    def test_missing_and_malformed_argument_fail_closed(self):
        self.assertEqual(self.c.send('11 5 -1 0 0'), 'ERR')

    def test_oversized_number_fails_closed(self):
        self.assertEqual(self.c.send(f'1 {2**64} 0'), 'ERR')

    def test_quit_does_not_wait_for_eof(self):
        self.assertEqual(self.c.send('0'), 'BYE')
        self.c.process.wait(timeout=5)

    def test_invalid_class_binding_consumes_its_name(self):
        self.assertEqual(self.c.send('9 999999 absent'), 'NO')
        cls = self.c.ok('5 0')
        self.assertEqual(self.c.ok(f'9 {cls} absent'), cls)
        self.assertEqual(self.c.ok('10 absent'), cls)

    def test_name_length_boundary(self):
        cls = self.c.ok('5 0')
        name = 'a' * 1024
        self.assertEqual(self.c.ok(f'9 {cls} {name}'), cls)
        self.assertEqual(self.c.ok(f'10 {name}'), cls)
        self.assertEqual(self.c.send('10 ' + name + 'a'), 'ERR')

    def test_eof_mid_command_fails_closed(self):
        result = subprocess.run([str(BINARY)], input=SEED+'11 5', text=True,
                                capture_output=True, timeout=5, check=True)
        self.assertEqual(result.stdout, 'SEED\nREADY\nERR\n')

    def test_empty_eof(self):
        result = subprocess.run([str(BINARY)], input=SEED, text=True, capture_output=True, timeout=5, check=True)
        self.assertEqual(result.stdout, 'SEED\nREADY\n')

    def test_seed_handshake_rejects_missing_malformed_and_overflowing_words(self):
        for seed in ['', '0', '0\n', '-1 0\n', '0 x\n', f'{MAX+1} 0\n', f'0 {MAX+1}\n']:
            with self.subTest(seed=seed):
                result = subprocess.run([str(BINARY)], input=seed, text=True, capture_output=True, timeout=5, check=True)
                self.assertEqual(result.stdout, 'SEED\nERR\n')
        result = subprocess.run([str(BINARY)], input=f'{MAX} {MAX}\n0\n', text=True, capture_output=True, timeout=5, check=True)
        self.assertEqual(result.stdout, 'SEED\nREADY\nBYE\n')

    def test_hash_resize_preserves_ids_and_duplicate_detection(self):
        count = 12000
        commands = [f'1 {i} {i+1}' for i in range(count)]
        commands += [f'1 {i} {i+1}' for i in reversed(range(count))]
        result = subprocess.run([str(BINARY)], input=SEED+'\n'.join(commands)+'\n0\n', text=True,
                                capture_output=True, timeout=10, check=True)
        replies = result.stdout.splitlines()
        self.assertEqual(replies[:2], ['SEED', 'READY'])
        self.assertEqual(replies[2:2+count], [f'OK {i+1}' for i in range(count)])
        self.assertEqual(replies[2+count:-1], [f'OK {i+1}' for i in reversed(range(count))])
        self.assertEqual(replies[-1], 'BYE')

    def test_hash_bucket_collisions_compare_full_formula_tuples(self):
        key = tuple(map(int, SEED.split()))
        buckets = {}
        # Find a real collision for this seed, without depending on native IDs.
        for i in range(1025):
            words = (1, i, i + 1)
            bucket = siphash(key, words) % 1024
            if bucket in buckets:
                first, second = buckets[bucket], words
                break
            buckets[bucket] = words
        else:
            self.fail('Pigeonhole principle violated')
        ids = [self.c.ok(f'1 {a} {b}') for _, a, b in [first, second]]
        self.assertNotEqual(*ids)
        # Revisit the older entry behind the newer bucket head, then the head.
        for words, expected in zip([first, second, first], [*ids, ids[0]]):
            _, a, b = words
            self.assertEqual(self.c.ok(f'1 {a} {b}'), expected)

    def test_seed_changes_hash_layout_without_changing_protocol_ids(self):
        commands = ''.join(f'1 {i} {i+1}\n' for i in range(1500))
        commands += '1 1 2\n1 1499 1500\n0\n'
        outputs = []
        for seed in ['0 0\n', SEED, f'{MAX} {MAX}\n']:
            result = subprocess.run([str(BINARY)], input=seed+commands, text=True,
                                    capture_output=True, timeout=5, check=True)
            outputs.append(result.stdout)
        self.assertEqual(outputs[0], outputs[1])
        self.assertEqual(outputs[1], outputs[2])


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--reference', type=Path, required=True)
    args, remaining = parser.parse_known_args()
    BINARY, REFERENCE = args.binary.resolve(), args.reference.resolve()
    unittest.main(argv=[sys.argv[0], *remaining])
