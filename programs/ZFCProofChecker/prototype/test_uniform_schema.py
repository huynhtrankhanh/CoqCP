import unittest

from uniform_schema import Arena


class Backend:
    def __init__(self):
        self.seen = []

    def template(self, value, rho, depth):
        self.seen.append(value)
        return ('template', value, rho, depth)

    def formula(self, value):
        return value

    def imp(self, p, q):
        return ('imp', p, q)

    def all(self, p):
        return ('all', p)

    def rename(self, p, mode, parameter):
        return ('rename', mode, parameter, p)

    def axiom_part(self, tag, p, left):
        return ('axiom_part', tag, p, left)


class Tests(unittest.TestCase):
    def test_hash_collisions_are_checked(self):
        a = Arena(lambda _: 0)
        p, q = a.template(('meta', 0)), a.template(('meta', 1))
        self.assertNotEqual(p, q)
        self.assertEqual(p, a.template(('meta', 0)))
        with self.assertRaises(ValueError):
            a.mp(a.imp(p, q), q)
        self.assertEqual(q, a.mp(a.imp(p, q), p))

    def test_normalized_templates_and_saved_formulas_match(self):
        a, backend = Arena(), Backend()
        atom = ('equal', 0, 0)
        p = a.concrete(atom)
        concrete = ('imp', atom, ('all', atom))
        saved = a.concrete(concrete)
        template = a.term(('literal', concrete))
        self.assertEqual(saved, template)
        self.assertEqual(a.expand(a.mp(saved, p), (), backend), ('all', atom))
        variable = ('equal-meta', 0, 1)
        quantified = a.term(('all', variable))
        self.assertEqual(a.expand(quantified, (), backend),
                         ('all', ('template', variable, (), 1)))

    def test_uniform_mp_rejects_accidental_instance_equality(self):
        a = Arena()
        xy = a.template(('equal-meta', 0, 1))
        reflexivity = a.axiom(5, i=0)
        other = a.template(('other',))
        implication = a.axiom(0, xy, other)
        with self.assertRaises(ValueError):
            a.mp(implication, reflexivity)

    def test_instance_visits_only_conclusion(self):
        a = Arena()
        p, q = a.template(('p',)), a.template(('q',))
        # MP(K(p,q), p) yields q -> p. The premise and the K axiom itself
        # need no traversal during expansion.
        conclusion = a.mp(a.axiom(0, p, q), p)
        for i in range(5000):
            a.axiom(0, a.template(('unused', i)), q)
        backend = Backend()
        result = a.expand(conclusion, ('class',), backend)
        self.assertEqual(result[0], 'imp')
        self.assertEqual(backend.seen, [('q',), ('p',)])

    def test_generalization_and_axiom_quantifier_depth(self):
        a, backend = Arena(), Backend()
        p = a.template(('p',))
        self.assertEqual(a.expand(a.generalize(p), (), backend),
                         ('all', ('template', ('p',), (), 1)))
        self.assertEqual(a.expand(a.all(p), (), backend),
                         ('all', ('template', ('p',), (), 0)))

    def test_instantiate_and_separation_apply_after_expansion(self):
        a, backend = Arena(), Backend()
        p = a.template(('p',))
        result = a.expand(a.axiom(3, p, j=7), (), backend)
        self.assertEqual(result[2], ('rename', 'instantiate', 7,
                                     ('template', ('p',), (), 0)))
        result = a.expand(a.axiom(15, p), (), backend)
        P = ('template', ('p',), (), 0)
        self.assertEqual(result, ('imp', ('axiom_part', 15, P, True),
                                  ('axiom_part', 15, P, False)))

    def test_all_axiom_conclusions(self):
        closed = {tag: ('closed', tag) for tag in (9, 10, 11, 12, 13, 14, 17)}
        a, backend = Arena(closed_axioms=closed), Backend()
        p, q, r = (a.template((x,)) for x in ('p', 'q', 'r'))
        P, Q, R = (('template', (x,), (), 0) for x in ('p', 'q', 'r'))
        I = backend.imp
        A = backend.all
        E = lambda i, j: ('equal', i, j)
        M = lambda i, j: ('member', i, j)
        F = ('false',)
        expected = {
            0: I(P, I(Q, P)),
            1: I(I(P, I(Q, R)), I(I(P, Q), I(P, R))),
            2: I(I(I(P, F), F), P),
            3: I(A(P), ('rename', 'instantiate', 2, P)),
            4: I(A(I(('rename', 'shift', 0, P), Q)), I(P, A(Q))),
            5: E(1, 1),
            6: I(E(1, 2), I(M(1, 3), M(2, 3))),
            7: I(E(1, 2), I(M(3, 1), M(3, 2))),
            8: I(E(1, 2), I(E(1, 3), E(2, 3))),
        }
        for tag in range(9, 18):
            expected[tag] = (I(('axiom_part', tag, P, True), ('axiom_part', tag, P, False))
                             if tag in (15, 16) else closed[tag])
        for tag, formula in expected.items():
            with self.subTest(tag=tag):
                root = a.axiom(tag, p, q, r, i=1, j=2, k=3)
                self.assertEqual(a.expand(root, (), backend), formula)

    def test_deep_dag_does_not_use_python_recursion(self):
        a, backend = Arena(), Backend()
        p = a.template(('p',))
        for _ in range(2000):
            p = a.generalize(p)
        a.expand(p, (), backend)
        self.assertEqual(backend.seen, [('p',)])


if __name__ == '__main__':
    unittest.main()
