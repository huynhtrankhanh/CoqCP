#!/usr/bin/env python3
"""Emit the repetitive CoqCP arena implementation and its axiom builders.

The result is ordinary CoqCP source, compiled to C++ and Coq by the repository
compiler. This generator does not extract Gallina or run a native proof kernel.
"""
from pathlib import Path

HERE = Path(__file__).resolve().parent
MAX = "18446744073709551615"


def loop256(body, stop, depth=0):
    if depth == 8:
        return body
    inside = loop256(body, stop, depth + 1)
    return f"range(4294967296, (bound{depth}) => {{\nif ({stop}) {{ ;('break') }}\n{inside}\n}})"


def procedure(name, locals, body):
    declarations = ", ".join(f"{key}: {kind}" for key, kind in locals.items())
    return f"procedure('{name}', {{ {declarations} }}, () => {{\n{body}\n}})\n"


def read_argument(name):
    return ("if (retrieve('meta', 8)[0] == 0) {\n"
            f"call('readNat', {{}})\nset('{name}', retrieve('meta', 11)[0])\n"
            "if (retrieve('meta', 14)[0] == 0) { store('meta', 8, [1]) }\n}\n")


def imp(a, b): return (3, a, b)
def all_(a): return (4, a)
def eq(a, b): return (1, str(a), str(b))
def mem(a, b): return (2, str(a), str(b))
def neg(a): return imp(a, "0")
def and_(a, b): return neg(imp(a, neg(b)))
def or_(a, b): return imp(neg(a), b)
def iff(a, b): return and_(imp(a, b), imp(b, a))
def ex(a): return neg(all_(neg(a)))
def rename(mode, p, shift="0", arg="0"): return ("rename", mode, p, shift, arg)


class Builder:
    def __init__(self):
        self.lines, self.locals, self.memo = [], {}, {}

    def emit(self, tree):
        if isinstance(tree, str):
            return tree
        if tree in self.memo:
            return self.memo[tree]
        if tree[0] == "rename":
            _, mode, p, shift, arg = tree
            p = self.emit(p)
            self.lines.append(f"call('rename', {{ node: {p}, mode: {mode}, shift: {shift}, arg: {arg} }})")
        else:
            tag, *children = tree
            if tag in [1, 2]:
                a, b = children
            elif tag == 3:
                a, b = map(self.emit, children)
            elif tag == 4:
                a, b = self.emit(children[0]), "0"
            else:
                raise ValueError(tag)
            self.lines.append(f"call('intern', {{ tag: {tag}, a: {a}, b: {b} }})")
        name = f"t{len(self.locals)}"
        self.locals[name] = "int64"
        self.lines.append(f"set('{name}', retrieve('meta', 0)[0])")
        result = f"get('{name}')"
        self.memo[tree] = result
        return result


def builder_procedure(name, arguments, tree, before=""):
    b = Builder()
    result = b.emit(tree)
    return procedure(name, {**arguments, **b.locals},
                     before + "\n" + "\n".join(b.lines) + f"\nstore('meta', 0, [{result}])")


def axiom_builder():
    p, q, r = "get('p')", "get('q')", "get('r')"
    ext = imp(all_(iff(mem(0, 1), mem(0, 2))), eq(0, 1))
    found = imp(ex(mem(0, 1)), ex(and_(mem(0, 1), all_(imp(mem(0, 1), neg(mem(0, 2)))))))
    pair = ex(and_(mem(1, 0), mem(2, 0)))
    union = ex(all_(all_(imp(mem(0, 1), imp(mem(1, 3), mem(0, 2))))))
    power = ex(all_(imp(all_(imp(mem(0, 1), mem(0, 3))), mem(0, 1))))
    infinity = ex(and_(ex(and_(mem(0, 1), all_(neg(mem(0, 1))))),
                       all_(imp(mem(0, 1), ex(and_(mem(0, 2), all_(iff(mem(0, 1), or_(mem(0, 2), eq(0, 2))))))))))
    separation = ex(all_(iff(mem(0, 1), and_(mem(0, 2), rename(2, p)))))
    replacement = imp(all_(imp(mem(0, 1), all_(all_(imp(rename(3, p), imp(rename(4, p), eq(1, 0))))))),
                      ex(all_(imp(ex(and_(mem(0, 3), rename(5, p))), mem(0, 1)))))
    nonempty = all_(imp(mem(0, 1), ex(mem(0, 1))))
    disjoint = all_(all_(imp(mem(1, 2), imp(mem(0, 2), imp(ex(and_(mem(0, 2), mem(0, 1))), eq(1, 0))))))
    transversal = ex(all_(imp(mem(0, 2), ex(and_(mem(0, 1), and_(mem(0, 2),
                         all_(imp(mem(0, 2), imp(mem(0, 3), eq(0, 1))))))))))
    cases = [imp(p, imp(q, p)), imp(imp(p, imp(q, r)), imp(imp(p, q), imp(p, r))),
             imp(neg(neg(p)), p), imp(all_(p), rename(1, p, arg=q)),
             imp(all_(imp(rename(0, p, shift="1"), q)), imp(p, all_(q))),
             eq(p, p), imp(eq(p, q), imp(mem(p, r), mem(q, r))),
             imp(eq(p, q), imp(mem(r, p), mem(r, q))),
             imp(eq(p, q), imp(eq(p, r), eq(q, r))),
             ext, found, pair, union, power, infinity, separation, replacement,
             imp(and_(nonempty, disjoint), transversal)]
    output, locals = [], dict(tag="int64", p="int64", q="int64", r="int64")
    for index, tree in enumerate(cases):
        b = Builder()
        result = b.emit(tree)
        locals.update(b.locals)
        if index in [0, 4]:
            valid = f"less({p}, retrieve('meta', 1)[0]) && less({q}, retrieve('meta', 1)[0])"
        elif index == 1:
            valid = f"less({p}, retrieve('meta', 1)[0]) && less({q}, retrieve('meta', 1)[0]) && less({r}, retrieve('meta', 1)[0])"
        elif index in [2, 3, 15, 16]:
            valid = f"less({p}, retrieve('meta', 1)[0])"
        else:
            valid = "true"
        output.append(f"if (get('tag') == {index} && ({valid})) {{\n" + "\n".join(b.lines)
                      + f"\nstore('meta', 0, [{result}])\nstore('meta', 13, [1])\n}}")
    return procedure("axiom", locals, "store('meta', 13, [0])\n" + "\n".join(output))


def commands():
    parts = []
    def case(op, args, body, valid="true"):
        reads = "".join(read_argument(arg) for arg in args)
        parts.append(f"if (get('op') == {op} && retrieve('meta', 8)[0] == 0) {{\n"
                     + reads + "if (retrieve('meta', 8)[0] == 0) {\n"
                     + f"if ({valid}) {{\n{body}\n}} else {{ call('no', {{}}) }}\n}}\n}}")
    formula = lambda x: f"less(get('{x}'), retrieve('meta', 1)[0])"
    cls = lambda x: f"less(get('{x}'), retrieve('meta', 2)[0])"
    theorem = lambda x: f"less(get('{x}'), retrieve('meta', 3)[0])"
    okay = "if (retrieve('meta', 8)[0] == 0) { call('ok', {value: retrieve('meta', 0)[0]}) }"
    case(0, [], "store('meta', 9, [1])\nrange('BYE\\n', (c) => { writeChar(c) })\n;('flush')")
    for op, tag in [(1, 1), (2, 2), (3, 3), (4, 4)]:
        args = ['a'] if op == 4 else ['a', 'b']
        valid = (formula('a') + (' && ' + formula('b') if op == 3 else '')) if op in [3, 4] else 'true'
        case(op, args, f"call('intern', {{tag: {tag}, a: get('a'), b: "
             + ("0" if op == 4 else "get('b')") + "})\n" + okay, valid)
    for op, kind in [(5, 0), (6, 1)]:
        case(op, ['a'], f"""
if (retrieve('meta', 2)[0] == {MAX}) {{ store('meta', 8, [1]) }} else {{
  grow('classes', retrieve('meta', 2)[0] + 1)
  store('classes', retrieve('meta', 2)[0], [{kind}, get('a')])
  call('ok', {{value: retrieve('meta', 2)[0]}})
  store('meta', 2, [retrieve('meta', 2)[0] + 1])
}}""", formula('a') if kind == 1 else 'true')
    for op, proc in [(7, 'classEqual'), (8, 'classMember')]:
        case(op, ['a', 'b'], f"call('{proc}', {{a: get('a'), b: get('b')}})\n" + okay,
             cls('a') + ' && ' + cls('b'))
    def read_name():
        return "call('readToken', {})\nif (retrieve('meta', 14)[0] == 0) { store('meta', 8, [1]) }\n"
    case(9, ['a'], read_name() + """
if (retrieve('meta', 8)[0] == 0) {
  if (!less(get('a'), retrieve('meta', 2)[0])) { call('no', {}) } else {
    call('bindName', {value: get('a'), kind: 0})
  }
}""")
    case(10, [], read_name() + """
if (retrieve('meta', 8)[0] == 0) {
  call('lookup', {})
  if (retrieve('meta', 0)[0] == 18446744073709551615 || retrieve('bindings', retrieve('meta', 0)[0])[4] != 0) { call('no', {}) } else {
    call('ok', {value: retrieve('bindings', retrieve('meta', 0)[0])[2]})
  }
}""")
    case(11, ['tag', 'a', 'b', 'c'], """
call('axiom', {tag: get('tag'), p: get('a'), q: get('b'), r: get('c')})
if (retrieve('meta', 13)[0] == 0) { call('no', {}) } else {
  call('appendTheorem', {node: retrieve('meta', 0)[0]})
}""")
    case(12, ['a', 'b'],
         "call('modusPonens', {implication: get('a'), antecedent: get('b')})",
         theorem('a') + ' && ' + theorem('b'))
    case(13, ['a'], "call('generalize', {theorem: get('a')})", theorem('a'))
    case(14, [], read_name() + """
if (retrieve('meta', 8)[0] == 0) {
  call('lookup', {})
  set('binding', retrieve('meta', 0)[0])
""" + read_argument('a') + """
  if (retrieve('meta', 8)[0] == 0) {
    if (get('binding') != 18446744073709551615 && retrieve('bindings', get('binding'))[4] == 0 && less(get('a'), retrieve('meta', 3)[0])) {
      call('setness', {cls: retrieve('bindings', get('binding'))[2]})
      if (retrieve('meta', 8)[0] == 0) {
        if (retrieve('meta', 0)[0] == retrieve('theorems', get('a'))[0]) {
          store('bindings', get('binding'), [retrieve('bindings', get('binding'))[0], retrieve('bindings', get('binding'))[1], retrieve('bindings', get('binding'))[2], 1, 0])
          call('ok', {value: retrieve('bindings', get('binding'))[2]})
        } else { call('no', {}) }
      }
    } else { call('no', {}) }
  }
}""")
    case(15, [], read_name() + """
if (retrieve('meta', 8)[0] == 0) {
  call('lookup', {})
  if (retrieve('meta', 0)[0] == 18446744073709551615 || retrieve('bindings', retrieve('meta', 0)[0])[4] != 0) { call('no', {}) } else {
    if (retrieve('bindings', retrieve('meta', 0)[0])[3] == 1) {
      range('SET\\n', (c) => { writeChar(c) })
    } else { range('CLASS\\n', (c) => { writeChar(c) }) }
    ;('flush')
  }
}""")
    case(16, [], """
if (retrieve('meta', 3)[0] == 0) { call('no', {}) } else {
  store('meta', 3, [retrieve('meta', 3)[0] - 1])
  call('ok', {value: retrieve('meta', 3)[0]})
}""")
    case(17, [], "store('meta', 3, [0])\ncall('ok', {value: 0})")
    case(18, ['a', 'b'], """
if (retrieve('theorems', get('a'))[0] == get('b')) {
  call('appendTheorem', {node: get('b')})
} else { call('no', {}) }
""", theorem('a') + ' && ' + formula('b'))
    case(19, ['a'], "call('ok', {value: retrieve('theorems', get('a'))[0]})", theorem('a'))
    case(20, ['a'], read_name() + """
if (retrieve('meta', 8)[0] == 0) {
  if (less(get('a'), retrieve('meta', 3)[0])) {
    call('bindName', {value: retrieve('theorems', get('a'))[0], kind: 1})
  } else { call('no', {}) }
}""")
    case(21, [], read_name() + """
if (retrieve('meta', 8)[0] == 0) {
  call('lookup', {})
  if (retrieve('meta', 0)[0] == 18446744073709551615 || retrieve('bindings', retrieve('meta', 0)[0])[4] != 1) {
    call('no', {})
  } else { call('appendTheorem', {node: retrieve('bindings', retrieve('meta', 0)[0])[2]}) }
}""")
    case(22, ['tag', 'a', 'b', 'c', 'node'], "call('schemaNode', {kind: get('tag'), a: get('a'), b: get('b'), c: get('c'), d: get('node')})")
    case(23, ['a'], read_name() + """
if (retrieve('meta', 8)[0] == 0) {
  if (less(get('a'), retrieve('meta', 16)[0]) && retrieve('schemaNodes', get('a'))[5] == 2) {
    call('bindName', {value: get('a'), kind: 2})
  } else { call('no', {}) }
}""")
    case(24, [], read_name() + """
if (retrieve('meta', 8)[0] == 0) {
  call('lookup', {})
  set('binding', retrieve('meta', 0)[0])
""" + read_argument('a') + """
  store('meta', 18, [1])
  range(get('a'), (i) => {
""" + read_argument('b') + """
    if (retrieve('meta', 8)[0] != 0) { ;('break') }
    if (!less(get('b'), retrieve('meta', 2)[0])) { store('meta', 18, [0]) }
    grow('schemaArguments', i + 1)
    store('schemaArguments', i, [get('b')])
  })
  if (retrieve('meta', 8)[0] == 0) {
    if (get('binding') == 18446744073709551615 || retrieve('bindings', get('binding'))[4] != 2) {
      call('no', {})
    } else {
      set('node', retrieve('bindings', get('binding'))[2])
      if (get('a') != retrieve('schemaNodes', get('node'))[6] || retrieve('meta', 18)[0] == 0) {
        call('no', {})
      } else {
        call('schemaInstance', {root: get('node')})
        if (retrieve('meta', 8)[0] == 0) {
          if (retrieve('meta', 18)[0] == 0) { call('no', {}) } else {
            call('appendTheorem', {node: retrieve('meta', 0)[0]})
          }
        }
      }
    }
  }
}""")
    for op in [25, 26]:
        response = """
    if (retrieve('bindings', retrieve('meta', 0)[0])[4] == 0) {
      range('CLASS\\n', (c) => { writeChar(c) })
    }
    if (retrieve('bindings', retrieve('meta', 0)[0])[4] == 1) {
      range('THEOREM\\n', (c) => { writeChar(c) })
    }
    if (retrieve('bindings', retrieve('meta', 0)[0])[4] == 2) {
      range('SCHEMA\\n', (c) => { writeChar(c) })
    }
    ;('flush')
""" if op == 25 else """
    if (retrieve('bindings', retrieve('meta', 0)[0])[4] != 2) { call('no', {}) } else {
      call('ok', {value: retrieve('schemaNodes', retrieve('bindings', retrieve('meta', 0)[0])[2])[6]})
    }
"""
        case(op, [], read_name() + """
if (retrieve('meta', 8)[0] == 0) {
  call('lookup', {})
  if (retrieve('meta', 0)[0] == 18446744073709551615) { call('no', {}) } else {
""" + response + "\n}}")
    return procedure('command', dict(op='int64', a='int64', b='int64', c='int64',
                                    tag='int64', node='int64', binding='int64'), """
call('readNat', {})
set('op', retrieve('meta', 11)[0])
if (retrieve('meta', 14)[0] == 0) {
  if (retrieve('meta', 7)[0] != 0 && retrieve('meta', 6)[0] == 0 && retrieve('meta', 8)[0] == 0) {
    store('meta', 9, [1])
  } else { store('meta', 8, [1]) }
} else {
  if (less(26, get('op'))) { store('meta', 8, [1]) }
""" + '\n'.join(parts) + "\n}\n" + """
if (retrieve('meta', 8)[0] != 0) {
  range('ERR\\n', (c) => { writeChar(c) })
  ;('flush')
  store('meta', 9, [1])
}
""")


def main():
    parts = [(HERE / "runtime.js.in").read_text()]
    evaluator = (HERE / "rename.js.in").read_text()
    parts.append(evaluator.replace("RENAME_LOOP", loop256(
        (HERE / "rename-step.js.in").read_text(),
        "retrieve('meta', 10)[0] == 0 || retrieve('meta', 8)[0] != 0")))
    parts.append(procedure("predicate", dict(cls="int64", shift="int64", arg="int64", value="int64"), """
if (retrieve('classes', get('cls'))[0] == 0) {
  set('value', retrieve('classes', get('cls'))[1])
  if (less(18446744073709551615 - get('value'), get('shift'))) { store('meta', 8, [1]) }
  if (retrieve('meta', 8)[0] == 0) {
    call('intern', {tag: 2, a: get('arg'), b: get('value') + get('shift')})
  }
} else {
  call('rename', {node: retrieve('classes', get('cls'))[1], mode: 6, shift: get('shift'), arg: get('arg')})
}
"""))
    b = Builder()
    class_eq = all_(iff("get('left')", "get('right')"))
    result = b.emit(class_eq)
    parts.append(procedure("classEqual", {**dict(a="int64", b="int64", left="int64", right="int64"), **b.locals}, """
if (retrieve('classes', get('a'))[0] == 0 && retrieve('classes', get('b'))[0] == 0) {
  call('intern', {tag: 1, a: retrieve('classes', get('a'))[1], b: retrieve('classes', get('b'))[1]})
} else {
  call('predicate', {cls: get('a'), shift: 1, arg: 0})
  set('left', retrieve('meta', 0)[0])
  call('predicate', {cls: get('b'), shift: 1, arg: 0})
  set('right', retrieve('meta', 0)[0])
""" + "\n".join(b.lines) + f"\nstore('meta', 0, [{result}])\n}}"))
    b = Builder()
    result = b.emit(ex(and_(all_(iff(mem(0, 1), "get('left')")), "get('right')")))
    parts.append(procedure("classMember", {**dict(a="int64", b="int64", left="int64", right="int64"), **b.locals}, """
if (retrieve('classes', get('a'))[0] == 0) {
  call('predicate', {cls: get('b'), shift: 0, arg: retrieve('classes', get('a'))[1]})
} else {
  call('predicate', {cls: get('a'), shift: 2, arg: 0})
  set('left', retrieve('meta', 0)[0])
  call('predicate', {cls: get('b'), shift: 1, arg: 0})
  set('right', retrieve('meta', 0)[0])
""" + "\n".join(b.lines) + f"\nstore('meta', 0, [{result}])\n}}"))
    setvar = Builder()
    sv = setvar.emit(ex(eq(0, "get('index') + 1")))
    abstraction = Builder()
    av = abstraction.emit(ex(all_(iff(mem(0, 1), "get('body')"))))
    parts.append(procedure("setness", {**dict(cls="int64", index="int64", body="int64"),
                                      **setvar.locals, **abstraction.locals}, """
if (retrieve('classes', get('cls'))[0] == 0) {
  set('index', retrieve('classes', get('cls'))[1])
  if (get('index') == 18446744073709551615) { store('meta', 8, [1]) }
  if (retrieve('meta', 8)[0] == 0) {
""" + "\n".join(setvar.lines) + f"\nstore('meta', 0, [{sv}])\n}}\n}} else {{\n" + """
  call('predicate', {cls: get('cls'), shift: 2, arg: 0})
  set('body', retrieve('meta', 0)[0])
""" + "\n".join(abstraction.lines) + f"\nstore('meta', 0, [{av}])\n}}"))
    parts.append(axiom_builder())
    parts.append((HERE / 'schemata.js.in').read_text())
    parts.append(commands())
    parts.append(procedure("main", {}, """
range('SEED\\n', (c) => { writeChar(c) })
;('flush')
call('readNat', {})
if (retrieve('meta', 14)[0] == 0) { store('meta', 8, [1]) } else {
  store('meta', 26, [retrieve('meta', 11)[0]])
  call('readNat', {})
  if (retrieve('meta', 14)[0] == 0) { store('meta', 8, [1]) } else {
    store('meta', 27, [retrieve('meta', 11)[0]])
  }
}
if (retrieve('meta', 8)[0] != 0) {
  range('ERR\\n', (c) => { writeChar(c) })
  ;('flush')
} else {
  store('meta', 20, [1024])
  call('intern', {tag: 0, a: 0, b: 0})
  range('READY\\n', (c) => { writeChar(c) })
  ;('flush')
  tapeEnd((ch) => {
    store('meta', 15, [coerceInt64(ch) + 1])
    call('command', {})
    if (retrieve('meta', 9)[0] != 0) { ;('break') }
  })
}
"""))
    (HERE.parent / "ZFCProofChecker.js").write_text("// Generated by generate.py from the adjacent source templates.\n" + "\n".join(parts))


if __name__ == "__main__":
    main()
