#!/usr/bin/env python3
"""Native protocol and independent finite-structure axiom readback checks."""
import argparse
from itertools import product
from pathlib import Path
import re
import subprocess
import unittest

BINARY = None


def session(commands):
    result = subprocess.run([str(BINARY)], input="\n".join(commands) + "\n",
                            text=True, capture_output=True, timeout=10, check=True)
    return result.stdout.splitlines()


def parse_formula(source):
    tokens = iter(re.findall(r"\(|\)|[^\s()]+", source))

    def read(token):
        if token != "(":
            return token
        values = []
        for token in tokens:
            if token == ")":
                return values
            values.append(read(token))
        raise AssertionError("incomplete formula output")

    return read(next(tokens))


def evaluate(formula, env, relation, domain):
    if formula == "false":
        return False
    operator, *args = formula
    if operator == "=":
        return env[int(args[0])] == env[int(args[1])]
    if operator == "in":
        return (env[int(args[0])], env[int(args[1])]) in relation
    if operator == "imp":
        return not evaluate(args[0], env, relation, domain) or evaluate(args[1], env, relation, domain)
    if operator == "all":
        return all(evaluate(args[0], (x, *env), relation, domain) for x in domain)
    raise AssertionError(f"unknown printed operator {operator}")


class InteractiveTests(unittest.TestCase):
    def test_proofs_references_undo_and_reset(self):
        self.assertEqual(session([
            "(axiom (refl 0))",
            "(prove false (ref 0))",
            "(prove (imp false (= 0 0)) (mp (ax (k (= 0 0) false)) (ref 0)))",
            "(prove (forall (= 0 0)) (gen (ref 1)))",
            "show", "undo", "reset", "undo", "quit",
        ]), ["OK 1", "REJECT 1", "OK 2", "OK 3",
             "0 (all (= 0 0))", "1 (imp false (= 0 0))", "2 (= 0 0)",
             "OK 2", "OK 0", "REJECT 0"])

    def test_forged_modus_ponens(self):
        self.assertEqual(session([
            "(prove false (mp (ax (k false (= 0 0))) (ax (refl 0))))",
            "(prove false (mp (ax (refl 0)) (ax (refl 0))))",
            "(prove false (ref 999999999999999999999999999999999))",
        ]), ["REJECT 0"] * 3)

    def test_class_elimination_and_capture(self):
        self.assertEqual(session([
            "(prove (class-in (set 5) (class (= 0 0))) (ax (refl 5)))",
            "(expand (class-in (set 1) (class (forall (in 1 2)))))",
            "(expand (class-in (set 3) (class (not (in 0 0)))))",
            "(expand (class-in (set 2) (class (class-in (set 0) (class (= 0 0))))))",
            "(expand (class= (set 0) (set 1)))",
        ]), ["OK 1", "(all (in 2 1))", "(imp (in 3 3) false)", "(= 2 2)", "(= 0 1)"])

    def test_big_indices_do_not_overflow(self):
        index = 2**180 + 3
        self.assertEqual(session([
            f"(prove (class-in (set {index}) (class (= 0 0))) (ax (refl {index})))",
            f"(expand (class-in (set {index}) (class (forall (in 1 2)))))",
        ]), ["OK 1", f"(all (in {index + 1} 1))"])

    def test_parse_errors_preserve_state(self):
        output = session(["(axiom (refl 0))", "(axiom (refl -1))",
                          "(axiom (refl 0)) garbage", "(prove false (bogus))",
                          "(prove (= 0 0) (ref 0))"])
        self.assertEqual(output[0], "OK 1")
        self.assertTrue(all(line.startswith("ERROR ") for line in output[1:4]))
        self.assertEqual(output[4], "OK 2")

    def test_reply_arrives_before_next_command(self):
        # A pipe remains open: publication cannot depend on EOF or the next input.
        with subprocess.Popen([str(BINARY)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                              text=True) as process:
            import select
            process.stdin.write("(axiom (refl 0))\n")
            process.stdin.flush()
            ready, _, _ = select.select([process.stdout], [], [], 5)
            self.assertTrue(ready, "checker did not flush its interactive response")
            self.assertEqual(process.stdout.readline(), "OK 1\n")
            process.stdin.write("quit\n")
            process.stdin.flush()
            process.wait(timeout=5)


class AxiomReadbackTests(unittest.TestCase):
    def test_axioms_against_independent_textbook_meanings(self):
        witnesses = ["ext", "found", "pair", "union", "power", "infinity", "choice",
                     "(sep (imp (in 0 2) (= 0 1)))",
                     "(repl (iff (in 0 2) (= 1 3)))"]
        output = session([f"(axiom {a})" for a in witnesses] + ["show"])
        self.assertEqual(output[:9], [f"OK {i}" for i in range(1, 10)])
        formulas = list(reversed([parse_formula(line.split(" ", 1)[1]) for line in output[9:]]))
        domain = (0, 1)
        for mask in range(16):
            relation = {edge for i, edge in enumerate(product(domain, repeat=2)) if mask & (1 << i)}
            m = lambda a, b: (a, b) in relation
            for env in product(domain, repeat=3):
                a, b, _ = env
                nonempty = lambda x: any(m(z, x) for z in domain)
                phi = lambda z: not m(z, b) or z == a
                psi = lambda x, y: m(x, a) == (y == b)
                functional = all(not (m(x, a) and psi(x, y) and psi(x, yp)) or y == yp
                                 for x, y, yp in product(domain, repeat=3))
                expected = [
                    not all(m(z, a) == m(z, b) for z in domain) or a == b,
                    not nonempty(a) or any(m(y, a) and all(not (m(z, y) and m(z, a))
                                                            for z in domain) for y in domain),
                    any(m(a, z) and m(b, z) for z in domain),
                    any(all(not (m(z, y) and m(y, a)) or m(z, u)
                            for y, z in product(domain, repeat=2)) for u in domain),
                    any(all(not all(not m(z, y) or m(z, a) for z in domain) or m(y, p)
                            for y in domain) for p in domain),
                    any(any(m(e, w) and not nonempty(e) for e in domain) and
                        all(not m(y, w) or any(m(s, w) and all(m(z, s) == (m(z, y) or z == y)
                                                             for z in domain) for s in domain)
                            for y in domain) for w in domain),
                    not (all(not m(x, a) or nonempty(x) for x in domain) and
                         all(not (m(x, a) and m(y, a) and any(m(z, x) and m(z, y) for z in domain))
                             or x == y for x, y in product(domain, repeat=2))) or
                    any(all(not m(x, a) or sum(m(y, x) and m(y, c) for y in domain) == 1
                            for x in domain) for c in domain),
                    any(all(m(z, y) == (m(z, a) and phi(z)) for z in domain) for y in domain),
                    not functional or any(all(not any(m(x, a) and psi(x, y) for x in domain)
                                              or m(y, image) for y in domain) for image in domain),
                ]
                for witness, encoded, meaning in zip(witnesses, formulas, expected):
                    with self.subTest(witness=witness, relation=mask, env=env):
                        self.assertEqual(evaluate(encoded, env, relation, domain), meaning)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True)
    args, remaining = parser.parse_known_args()
    BINARY = args.binary.resolve()
    unittest.main(argv=[__file__, *remaining])
