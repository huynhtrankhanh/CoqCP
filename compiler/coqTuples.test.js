import { CoqCPASTTransformer } from './parse'
import { sortModules } from './dependencyGraph'
import { validateAST } from './validateAST'
import { coqCodegen } from './coqCodegen'
import { execFileSync } from 'child_process'
import { mkdtempSync, writeFileSync, rmSync } from 'fs'
import { tmpdir } from 'os'
import path from 'path'

test('Rocq accepts every projection of a heterogeneous tuple', () => {
  const source = `
    environment({ data: array([int64, int8, int16, int32, int16], 1) })
    procedure('main', { a: int64, b: int8, c: int16, d: int32, e: int16 }, () => {
      store('data', 0, [9, coerceInt8(8), coerceInt16(5), coerceInt32(7), coerceInt16(6)])
      set('a', retrieve('data', 0)[0])
      set('b', retrieve('data', 0)[1])
      set('c', retrieve('data', 0)[2])
      set('d', retrieve('data', 0)[3])
      set('e', retrieve('data', 0)[4])
    })`
  const modules = sortModules([new CoqCPASTTransformer(source).transform()])
  expect(validateAST(modules)).toEqual([])
  const directory = mkdtempSync(path.join(tmpdir(), 'coqcp-tuples-'))
  try {
    const filename = path.join(directory, 'Tuples.v')
    writeFileSync(filename, coqCodegen(modules))
    execFileSync('/opt/rocq/9.3.0/bin/rocq', [
      'compile',
      '-q',
      '-R',
      path.resolve(__dirname, '../theories'),
      'CoqCP',
      filename,
    ])
  } finally {
    rmSync(directory, { recursive: true, force: true })
  }
}, 30000)
