"""Standalone design prototype; not a checker and not connected to production.

Leaves and transformations are interpreted by a caller-supplied backend. The
production implementation must prove that backend implements Schemata.v. Hashes
are only indexes: equality of complete node keys is always checked.
"""


class Arena:
    def __init__(self, hash_key=hash, closed_axioms=None):
        self.hash_key = hash_key
        self.closed_axioms = closed_axioms or {}
        self.nodes = []
        self.buckets = {}

    def intern(self, kind, *args):
        key = (kind,) + args
        bucket = self.buckets.setdefault(self.hash_key(key), [])
        for node in bucket:
            if self.nodes[node] == key:
                return node
        node = len(self.nodes)
        self.nodes.append(key)
        bucket.append(node)
        return node

    def template(self, value):
        # value is a hashable structural representation, not an input node ID.
        return self.intern('template', value)

    def formula(self, value):
        return self.intern('formula', value)

    def concrete(self, value):
        """Expose implications and quantifiers in a concrete formula."""
        if value[0] == 'imp':
            return self.imp(self.concrete(value[1]), self.concrete(value[2]))
        if value[0] == 'all':
            return self.all(self.concrete(value[1]))
        return self.formula(value)

    def term(self, value):
        """Normalize the formula-template constructors used by certification."""
        if value[0] == 'literal':
            return self.concrete(value[1])
        if value[0] == 'imp':
            return self.imp(self.term(value[1]), self.term(value[2]))
        if value[0] == 'all':
            return self.generalize(self.term(value[1]))
        return self.template(value)

    def check(self, node):
        if type(node) is not int or not 0 <= node < len(self.nodes):
            raise ValueError('unknown symbolic node')

    def imp(self, p, q):
        self.check(p)
        self.check(q)
        return self.intern('imp', p, q)

    def all(self, p):
        # An object-language quantifier does not itself lift schema arguments.
        self.check(p)
        return self.intern('all', p)

    def rename(self, p, mode, parameter=0):
        self.check(p)
        return self.intern('rename', p, mode, parameter)

    def axiom(self, tag, p=None, q=None, r=None, i=0, j=0, k=0):
        """Construct an axiom conclusion, rejecting unsupported tags/arguments."""
        if tag in (0, 1, 2, 3, 4, 15, 16) and p is None:
            raise ValueError('missing p')
        if tag in (0, 1, 4) and q is None:
            raise ValueError('missing q')
        if tag == 1 and r is None:
            raise ValueError('missing r')
        if tag in (0, 1, 2, 3, 4, 15, 16):
            self.check(p)
        if tag in (0, 1, 4):
            self.check(q)
        if tag == 1:
            self.check(r)
        imp = self.imp
        if tag == 0:
            return imp(p, imp(q, p))
        if tag == 1:
            return imp(imp(p, imp(q, r)), imp(imp(p, q), imp(p, r)))
        if tag == 2:
            false = self.formula(('false',))
            return imp(imp(imp(p, false), false), p)
        if tag == 3:
            return imp(self.all(p), self.rename(p, 'instantiate', j))
        if tag == 4:
            return imp(self.all(imp(self.rename(p, 'shift'), q)), imp(p, self.all(q)))
        if tag in (6, 7, 8):
            eq = lambda x, y: self.formula(('equal', x, y))
            mem = lambda x, y: self.formula(('member', x, y))
            if tag == 6:
                return imp(eq(i, j), imp(mem(i, k), mem(j, k)))
            if tag == 7:
                return imp(eq(i, j), imp(mem(k, i), mem(k, j)))
            return imp(eq(i, j), imp(eq(i, k), eq(j, k)))
        if tag == 5:
            return self.formula(('equal', i, i))
        if tag in (9, 10, 11, 12, 13, 14, 17):
            if tag not in self.closed_axioms:
                raise ValueError('missing closed axiom formula')
            return self.concrete(self.closed_axioms[tag])
        if tag in (15, 16):
            return imp(self.intern('axiom_part', tag, p, True),
                       self.intern('axiom_part', tag, p, False))
        raise ValueError('unknown axiom')

    def mp(self, implication, premise):
        self.check(implication)
        self.check(premise)
        node = self.nodes[implication]
        if node[0] != 'imp' or node[1] != premise:
            raise ValueError('not a uniformly valid modus ponens')
        return node[2]

    def generalize(self, conclusion):
        self.check(conclusion)
        return self.intern('gen', conclusion)

    def expand(self, root, rho, backend):
        """Evaluate only the conclusion DAG, memoized by (node, depth).

        backend provides template(value, rho, depth), axiom_part(tag, p, left),
        formula(value), rename(formula, mode, parameter), imp(p,q),
        and all(p). The actual implementation must use capture-avoiding
        operations and match the verified Rocq semantics exactly.
        """
        self.check(root)
        values = {}
        stack = [(root, 0, False)]
        while stack:
            node, depth, ready = stack.pop()
            key = (node, depth)
            if key in values:
                continue
            n = self.nodes[node]
            kind = n[0]
            children = []
            if kind == 'imp':
                children = [(n[1], depth), (n[2], depth)]
            elif kind in ('all', 'rename'):
                children = [(n[1], depth)]
            elif kind == 'gen':
                children = [(n[1], depth + 1)]
            elif kind == 'axiom_part':
                children = [(n[2], depth)]
            if not ready and children:
                stack.append((node, depth, True))
                stack.extend((child, d, False) for child, d in reversed(children) if (child, d) not in values)
                continue
            get = lambda index: values[children[index]]
            if kind == 'template':
                result = backend.template(n[1], rho, depth)
            elif kind == 'formula':
                result = backend.formula(n[1])
            elif kind == 'imp':
                result = backend.imp(get(0), get(1))
            elif kind == 'all':
                result = backend.all(get(0))
            elif kind == 'gen':
                result = backend.all(get(0))
            elif kind == 'rename':
                result = backend.rename(get(0), n[2], n[3])
            elif kind == 'axiom_part':
                result = backend.axiom_part(n[1], get(0), n[3])
            else:
                raise ValueError('invalid node')
            values[key] = result
        return values[(root, 0)]
