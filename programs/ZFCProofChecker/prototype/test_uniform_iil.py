#!/usr/bin/env python3
"""Compile and run the unconnected IIL interner in a private temporary build."""
import subprocess
import tempfile
import random
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
SOURCE = ROOT / 'programs/ZFCProofChecker.js'
SYMBOLS = ROOT / 'programs/ZFCProofChecker/uniform-symbols.js.in'
MEMO = ROOT / 'programs/ZFCProofChecker/uniform-memo.js.in'
EVAL = ROOT / 'programs/ZFCProofChecker/uniform-eval.js.in'


def main():
    source = SOURCE.read_text().rsplit("procedure('main',", 1)[0]
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
  uniformBuckets: array([int64], 1024),''', 1)
    source += SYMBOLS.read_text() + MEMO.read_text() + EVAL.read_text() + r'''
procedure('main', {x: int64, y: int64, implication: int64, bad: int64}, () => {
  store('meta', 20, [1024])
  store('meta', 26, [506097522914230528])
  store('meta', 27, [1084818905618843912])
  call('intern', {tag: 0, a: 0, b: 0})
  set('bad', 0)
  call('uniformMemoPutNew', {node: 0, depth: 0, value: 0})
  if (retrieve('meta', 8)[0] != 1) { set('bad', 1) }
  store('meta', 8, [0])
  call('uniformIntern', {tag: 1, a: 7, b: 0})
  set('x', retrieve('meta', 0)[0])
  call('uniformIntern', {tag: 1, a: 8, b: 0})
  set('y', retrieve('meta', 0)[0])
  if (get('x') == get('y')) { set('bad', 1) }
  call('uniformIntern', {tag: 2, a: get('x'), b: get('y')})
  set('implication', retrieve('meta', 0)[0])
  store('meta', 18, [1])
  call('uniformMP', {implication: get('implication'), antecedent: get('x')})
  if (retrieve('meta', 18)[0] != 1 || retrieve('meta', 0)[0] != get('y')) { set('bad', 1) }
  call('uniformMP', {implication: get('implication'), antecedent: get('y')})
  if (retrieve('meta', 18)[0] != 0) { set('bad', 1) }
  call('uniformLogicalAxiom', {tag: 0, p: get('x'), q: get('y')})
  set('implication', retrieve('meta', 0)[0])
  store('meta', 18, [1])
  call('uniformMP', {implication: get('implication'), antecedent: get('x')})
  set('implication', retrieve('meta', 0)[0])
  call('uniformMP', {implication: get('implication'), antecedent: get('y')})
  if (retrieve('meta', 18)[0] != 1 || retrieve('meta', 0)[0] != get('x')) { set('bad', 1) }
  call('uniformAxiomPartPair', {axiom: 23})
  set('implication', retrieve('meta', 0)[0])
  call('uniformIntern', {tag: 7, a: 23, b: 1})
  store('meta', 18, [1])
  call('uniformMP', {implication: get('implication'), antecedent: retrieve('meta', 0)[0]})
  set('x', retrieve('meta', 0)[0])
  call('uniformIntern', {tag: 7, a: 23, b: 0})
  if (retrieve('meta', 18)[0] != 1 || retrieve('meta', 0)[0] != get('x')) { set('bad', 1) }
  call('uniformIntern', {tag: 1, a: 7, b: 0})
  set('x', retrieve('meta', 0)[0])
  range(2500, (i) => { call('uniformIntern', {tag: 9, a: i, b: 0}) })
  if (retrieve('uniformState', 0)[1] != 4096) { set('bad', 1) }
  call('uniformIntern', {tag: 1, a: 7, b: 0})
  if (retrieve('meta', 0)[0] != get('x')) { set('bad', 1) }
  call('uniformAtom', {tag: 1, a: 2, b: 3})
  set('x', retrieve('meta', 0)[0])
  call('uniformAtom', {tag: 1, a: 2, b: 3})
  if (retrieve('meta', 0)[0] != get('x')) { set('bad', 1) }
  call('intern', {tag: 1, a: 2, b: 2})
  set('y', retrieve('meta', 0)[0])
  grow('schemaNodes', 6)
  store('schemaNodes', 0, [2, get('y'), 0, 0, 0, 1, 0])
  store('schemaNodes', 1, [8, 0, 0, 0, 0, 2, 0])
  store('schemaNodes', 2, [8, 5, 2, 0, 0, 2, 0])
  store('schemaNodes', 3, [9, 1, 2, 0, 0, 2, 0])
  store('schemaNodes', 4, [8, 5, 3, 0, 0, 2, 0])
  store('schemaNodes', 5, [9, 1, 4, 0, 0, 2, 0])
  store('meta', 16, [6])
  call('uniformCompile', {root: 3})
  if (retrieve('meta', 18)[0] != 1 || retrieve('uniformNodes', retrieve('meta', 0)[0])[0] != 2) { set('bad', 1) }
  call('uniformEvaluate', {root: retrieve('meta', 0)[0]})
  set('x', retrieve('meta', 0)[0])
  store('meta', 18, [1])
  call('schemaInstance', {root: 3})
  if (retrieve('meta', 18)[0] != 1 || retrieve('meta', 0)[0] != get('x')) { set('bad', 1) }
  call('uniformCompile', {root: 5})
  if (retrieve('meta', 18)[0] != 0) { set('bad', 1) }
  grow('schemaNodes', 24)
  range(18, (tag) => {
    store('schemaNodes', tag + 6, [8, tag, 0, 0, 0, 2, 0])
    if (less(4, tag) && less(tag, 9)) { store('schemaNodes', tag + 6, [8, tag, 37, 53, 92, 2, 0]) }
  })
  store('meta', 16, [24])
  range(18, (tag) => {
    call('uniformCompile', {root: tag + 6})
    if (retrieve('meta', 18)[0] != 1 || retrieve('meta', 8)[0] != 0) { set('bad', 1) }
    call('uniformEvaluate', {root: retrieve('meta', 0)[0]})
    set('x', retrieve('meta', 0)[0])
    store('meta', 18, [1])
    call('schemaInstance', {root: tag + 6})
    if (retrieve('meta', 18)[0] != 1 || retrieve('meta', 0)[0] != get('x')) { set('bad', 1); writeChar(coerceInt8(tag + 65)) }
  })
  call('uniformMemoReset', {})
  range(2500, (i) => { call('uniformMemoPutNew', {node: i, depth: i + 1, value: i + 2}) })
  if (retrieve('uniformMemoState', 0)[1] != 4096) { set('bad', 1) }
  range(2500, (i) => {
    call('uniformMemoGet', {node: i, depth: i + 1})
    if (retrieve('uniformMemoState', 0)[2] != 1 || retrieve('uniformMemoState', 0)[3] != i + 2) { set('bad', 1) }
  })
  call('uniformMemoGet', {node: 123, depth: 999})
  if (retrieve('uniformMemoState', 0)[2] != 0) { set('bad', 1) }
  call('uniformMemoReset', {})
  call('uniformMemoGet', {node: 123, depth: 124})
  if (retrieve('uniformMemoState', 0)[2] != 0) { set('bad', 1) }
  call('schemaClass', {kind: 0, value: 0})
  grow('schemaArguments', 1)
  store('schemaArguments', 0, [retrieve('meta', 0)[0]])
  call('uniformIntern', {tag: 10, a: 0, b: 0})
  set('x', retrieve('meta', 0)[0])
  call('uniformIntern', {tag: 24, a: get('x'), b: get('x')})
  call('uniformIntern', {tag: 1, a: retrieve('meta', 0)[0], b: 0})
  call('uniformIntern', {tag: 4, a: retrieve('meta', 0)[0], b: 0})
  set('implication', retrieve('meta', 0)[0])
  call('uniformEvaluate', {root: get('implication')})
  set('x', retrieve('meta', 0)[0])
  if (retrieve('uniformMemoState', 0)[0] != 4) { set('bad', 1) }
  call('intern', {tag: 1, a: 1, b: 1})
  call('intern', {tag: 4, a: retrieve('meta', 0)[0], b: 0})
  if (retrieve('meta', 0)[0] != get('x')) { set('bad', 1) }
  // The same symbolic subexpression occurs both outside and underneath a
  // binder. Memoization must distinguish its two substitution depths.
  call('uniformIntern', {tag: 40, a: 0, b: 0})
  set('x', retrieve('meta', 0)[0])
  call('uniformIntern', {tag: 44, a: get('x'), b: get('x')})
  call('uniformIntern', {tag: 1, a: retrieve('meta', 0)[0], b: 0})
  set('x', retrieve('meta', 0)[0])
  call('uniformIntern', {tag: 4, a: get('x'), b: 0})
  call('uniformIntern', {tag: 2, a: get('x'), b: retrieve('meta', 0)[0]})
  call('uniformEvaluate', {root: retrieve('meta', 0)[0]})
  set('x', retrieve('meta', 0)[0])
  call('intern', {tag: 1, a: 0, b: 0})
  set('y', retrieve('meta', 0)[0])
  call('intern', {tag: 1, a: 1, b: 1})
  call('intern', {tag: 4, a: retrieve('meta', 0)[0], b: 0})
  call('intern', {tag: 3, a: get('y'), b: retrieve('meta', 0)[0]})
  if (retrieve('meta', 0)[0] != get('x')) { set('bad', 1) }
  call('intern', {tag: 1, a: 0, b: 0})
  set('y', retrieve('meta', 0)[0])
  call('uniformConcrete', {root: get('y')})
  call('uniformIntern', {tag: 6, a: retrieve('meta', 0)[0], b: 3})
  call('uniformEvaluate', {root: retrieve('meta', 0)[0]})
  set('x', retrieve('meta', 0)[0])
  call('intern', {tag: 1, a: 3, b: 3})
  if (retrieve('meta', 0)[0] != get('x')) { set('bad', 1) }
  call('uniformConcrete', {root: get('y')})
  call('uniformIntern', {tag: 30, a: 15, b: retrieve('meta', 0)[0]})
  call('uniformIntern', {tag: 31, a: retrieve('meta', 0)[0], b: 0})
  call('uniformIntern', {tag: 32, a: retrieve('meta', 0)[0], b: 0})
  call('uniformIntern', {tag: 33, a: retrieve('meta', 0)[0], b: 0})
  call('uniformIntern', {tag: 34, a: retrieve('meta', 0)[0], b: 0})
  call('uniformAxiomPartPair', {axiom: retrieve('meta', 0)[0]})
  call('uniformEvaluate', {root: retrieve('meta', 0)[0]})
  set('x', retrieve('meta', 0)[0])
  call('axiom', {tag: 15, p: get('y'), q: 0, r: 0})
  if (retrieve('meta', 0)[0] != get('x')) { set('bad', 1) }
  call('schemaClass', {kind: 0, value: 12})
  set('x', retrieve('meta', 0)[0])
  call('schemaClass', {kind: 0, value: 12})
  set('y', retrieve('meta', 0)[0])
  if (get('x') == get('y')) { set('bad', 1) }
  grow('schemaNodes', 28)
  store('schemaNodes', 24, [1, get('x'), 0, 0, 0, 0, 0])
  store('schemaNodes', 25, [1, get('y'), 0, 0, 0, 0, 0])
  store('schemaNodes', 26, [8, 15, 0, 5, 0, 2, 0])
  store('schemaNodes', 27, [8, 15, 0, 6, 0, 2, 0])
  store('meta', 16, [28])
  call('uniformCompile', {root: 27})
  if (retrieve('uniformCompiled', 24)[0] != retrieve('uniformCompiled', 25)[0]) { set('bad', 1) }
  if (retrieve('uniformTemplates', 24)[0] != retrieve('uniformTemplates', 25)[0]) { set('bad', 1) }
  if (retrieve('uniformCompiled', 26)[0] == retrieve('uniformCompiled', 27)[0]) { set('bad', 1) }
  grow('schemaNodes', 31)
  store('schemaNodes', 28, [0, 0, 0, 0, 0, 0, 1])
  store('schemaNodes', 29, [4, 28, 28, 0, 0, 1, 1])
  store('schemaNodes', 30, [8, 0, 29, 29, 0, 2, 1])
  store('meta', 16, [31])
  call('uniformCompile', {root: 30})
  call('uniformEvaluate', {root: retrieve('meta', 0)[0]})
  set('x', retrieve('meta', 0)[0])
  store('meta', 18, [1])
  call('schemaInstance', {root: 30})
  if (retrieve('meta', 18)[0] != 1 || retrieve('meta', 0)[0] != get('x')) { set('bad', 1) }
  grow('schemaNodes', 36)
  store('schemaNodes', 31, [3, 29, 0, 0, 0, 0, 1])
  store('schemaNodes', 32, [5, 31, 28, 0, 0, 1, 1])
  store('schemaNodes', 33, [7, 32, 0, 0, 0, 1, 1])
  store('schemaNodes', 34, [8, 0, 33, 29, 0, 2, 1])
  store('schemaNodes', 35, [10, 34, 0, 0, 0, 2, 1])
  store('meta', 16, [36])
  call('intern', {tag: 1, a: 0, b: 1})
  call('schemaClass', {kind: 1, value: retrieve('meta', 0)[0]})
  store('schemaArguments', 0, [retrieve('meta', 0)[0]])
  call('uniformCompile', {root: 35})
  call('uniformEvaluate', {root: retrieve('meta', 0)[0]})
  set('x', retrieve('meta', 0)[0])
  store('meta', 18, [1])
  call('schemaInstance', {root: 35})
  if (retrieve('meta', 18)[0] != 1 || retrieve('meta', 0)[0] != get('x')) { set('bad', 1) }
  // Reusing a compiled conclusion must not reuse memoized values from a
  // previous substitution. Compare both results to the existing checker.
  set('y', retrieve('schemaArguments', 0)[0])
  call('schemaClass', {kind: 0, value: 2})
  store('schemaArguments', 0, [retrieve('meta', 0)[0]])
  call('uniformCompile', {root: 30})
  call('uniformEvaluate', {root: retrieve('meta', 0)[0]})
  set('x', retrieve('meta', 0)[0])
  store('meta', 18, [1])
  call('schemaInstance', {root: 30})
  if (retrieve('meta', 18)[0] != 1 || retrieve('meta', 0)[0] != get('x')) { set('bad', 1) }
  call('schemaClass', {kind: 0, value: 4})
  store('schemaArguments', 0, [retrieve('meta', 0)[0]])
  call('uniformCompile', {root: 30})
  call('uniformEvaluate', {root: retrieve('meta', 0)[0]})
  if (retrieve('meta', 0)[0] == get('x')) { set('bad', 1) }
  set('x', retrieve('meta', 0)[0])
  store('meta', 18, [1])
  call('schemaInstance', {root: 30})
  if (retrieve('meta', 18)[0] != 1 || retrieve('meta', 0)[0] != get('x')) { set('bad', 1) }
  store('schemaArguments', 0, [get('y')])
  // RANDOM_CASES
  // Separation renames its formula parameter. If that rename overflows,
  // axiom-part evaluation must propagate the fatal flag without examining a
  // purported result formula.
  call('intern', {tag: 1, a: 18446744073709551615, b: 18446744073709551615})
  call('uniformConcrete', {root: retrieve('meta', 0)[0]})
  call('uniformIntern', {tag: 30, a: 15, b: retrieve('meta', 0)[0]})
  call('uniformIntern', {tag: 31, a: retrieve('meta', 0)[0], b: 0})
  call('uniformIntern', {tag: 32, a: retrieve('meta', 0)[0], b: 0})
  call('uniformIntern', {tag: 33, a: retrieve('meta', 0)[0], b: 0})
  call('uniformIntern', {tag: 34, a: retrieve('meta', 0)[0], b: 0})
  call('uniformAxiomPartPair', {axiom: retrieve('meta', 0)[0]})
  call('uniformEvaluate', {root: retrieve('meta', 0)[0]})
  if (retrieve('meta', 8)[0] != 1) { set('bad', 1) }
  store('meta', 8, [0])
  call('schemaClass', {kind: 0, value: 18446744073709551615})
  store('schemaArguments', 0, [retrieve('meta', 0)[0]])
  call('uniformIntern', {tag: 40, a: 0, b: 0})
  set('x', retrieve('meta', 0)[0])
  call('uniformIntern', {tag: 44, a: get('x'), b: get('x')})
  call('uniformIntern', {tag: 1, a: retrieve('meta', 0)[0], b: 0})
  call('uniformIntern', {tag: 4, a: retrieve('meta', 0)[0], b: 0})
  call('uniformEvaluate', {root: retrieve('meta', 0)[0]})
  if (retrieve('meta', 8)[0] != 1) { set('bad', 1) }
  store('meta', 8, [0])
  if (retrieve('meta', 8)[0] != 0) { set('bad', 1) }
  if (get('bad') == 0) { range('PASS\n', (c) => { writeChar(c) }) }
  else { range('FAIL\n', (c) => { writeChar(c) }) }
  ;('flush')
})
'''
    rng = random.Random(78641)
    formulas = [29, 32, 33]
    generated = []
    for case in range(24):
        node = 36 + case * 3
        left, right = rng.choice(formulas), rng.choice(formulas)
        kind = rng.choice((6, 7))
        tag = rng.choice((0, 1, 2, 3, 4, 15, 16))
        generated.extend([
            f"grow('schemaNodes', {node + 3})",
            f"store('schemaNodes', {node}, [{kind}, {left}, {right}, 0, 0, 1, 1])",
            f"store('schemaNodes', {node + 1}, [8, {tag}, {node}, {right}, {left}, 2, 1])",
            f"store('schemaNodes', {node + 2}, [10, {node + 1}, 0, 0, 0, 2, 1])",
            f"store('meta', 16, [{node + 3}])",
            f"call('uniformCompile', {{root: {node + 2}}})",
            "if (retrieve('meta', 18)[0] != 1) { set('bad', 1) }",
            "call('uniformEvaluate', {root: retrieve('meta', 0)[0]})",
            "set('x', retrieve('meta', 0)[0])",
            "store('meta', 18, [1])",
            f"call('schemaInstance', {{root: {node + 2}}})",
            "if (retrieve('meta', 18)[0] != 1 || retrieve('meta', 0)[0] != get('x')) { set('bad', 1) }",
        ])
        formulas.append(node)
    source = source.replace('// RANDOM_CASES', '\n'.join(generated))
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp)
        js = out / 'Test.js'
        js.write_text(source)
        subprocess.run(['node', str(ROOT / 'compiler/dist/cli.js'), str(out / 'Test.v'),
                        str(out / 'Test.cpp'), str(js), str(ROOT / 'programs/IO/PrintInt64.js')],
                       cwd=ROOT, check=True)
        subprocess.run(['g++', '-std=c++20', '-O2', str(out / 'Test.cpp'), '-o', str(out / 'test')],
                       cwd=ROOT, check=True)
        result = subprocess.run([str(out / 'test')], text=True, capture_output=True, check=True)
        if result.stdout != 'PASS\n':
            raise AssertionError(result.stdout + result.stderr)
    print('uniform IIL interner: PASS')


if __name__ == '__main__':
    main()
