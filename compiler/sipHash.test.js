import { execFileSync } from 'child_process'
import path from 'path'

test('checker IIL SipHash matches the reference vector and independent oracle', () => {
  const output = execFileSync(
    'python3',
    [
      path.resolve(
        __dirname,
        '../verification/zfc-virtual-classes/imperative/test_siphash.py'
      ),
    ],
    { encoding: 'utf8' }
  )
  expect(output).toContain('published 24-byte vector')
  expect(output).toContain('66 additional oracle cases passed')
}, 30000)
