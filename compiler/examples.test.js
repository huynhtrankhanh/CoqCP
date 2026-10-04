import { readFileSync, mkdtempSync, writeFileSync, rmSync } from 'fs'
import { execFileSync, spawnSync } from 'child_process'
import path from 'path'
import { tmpdir } from 'os'
import { CoqCPASTTransformer } from './parse'
import { sortModules } from './dependencyGraph'
import { validateAST } from './validateAST'
import { cppCodegen } from './cppCodegen'

const examples = [
  ['Knapsack', '3 5\n2 3\n3 4\n4 5\n', '7\n'],
  ['BuyLowSellHigh', '5\n1 2 3 4 5\n', '6\n'],
  ['DisjointSetUnion', '3\n0 1\n1 2\n0 2\n', '2\n3\n3\n'],
  ['MajorityElement', '5\n1 2 2 2 3\n', '2\n'],
  ['SimpleProgram', '', 'The number is 2'],
  ['FenwickTree', '3 3\n1 2 3\n2 1 3\n1 2 5\n2 1 3\n', '6\n9\n'],
  ['llmGeneratedCode/BubbleSort', '4\n4 2 3 1\n', '1\n2\n3\n4\n'],
  ['llmGeneratedCode/MaxElement', '4\n3 9 2 5\n', '9\n'],
]

test.each(examples)(
  'competitive example %s compiles and runs',
  (name, input, output) => {
    const configPath = path.resolve(
      __dirname,
      '../programs',
      name + '.module.json'
    )
    const config = JSON.parse(readFileSync(configPath, 'utf8'))
    expect(config.type).toBe('competitive')
    expect(config.cppOutput.endsWith('.cpp')).toBe(true)
    const modules = sortModules(
      config.inputs.map((filename) =>
        new CoqCPASTTransformer(
          readFileSync(path.resolve(path.dirname(configPath), filename), 'utf8')
        ).transform()
      )
    )
    expect(validateAST(modules)).toEqual([])
    const directory = mkdtempSync(path.join(tmpdir(), 'coqcp-example-'))
    try {
      const source = path.join(directory, 'example.cpp')
      const executable = path.join(directory, 'example')
      writeFileSync(source, cppCodegen(modules))
      execFileSync('g++', ['-std=c++20', '-O1', source, '-o', executable])
      expect(execFileSync(executable, { input, encoding: 'utf8' })).toBe(output)
      if (
        name === 'Knapsack' ||
        name.endsWith('MaxElement') ||
        name === 'BuyLowSellHigh'
      ) {
        expect(
          execFileSync(executable, {
            input: name === 'Knapsack' ? '0 0\n' : '0\n',
            encoding: 'utf8',
          })
        ).toBe('0\n')
      }
      if (name.endsWith('BubbleSort')) {
        expect(
          execFileSync(executable, { input: '0\n', encoding: 'utf8' })
        ).toBe('')
      }
    } finally {
      rmSync(directory, { recursive: true, force: true })
    }
  }
)

test('CLI rejects the removed blockchain option and configuration', () => {
  const cli = path.resolve(__dirname, 'dist/cli.js')
  expect(
    spawnSync(process.execPath, [cli, '--blockchain'], { encoding: 'utf8' })
      .stderr
  ).toContain("unknown option '--blockchain'")
  const directory = mkdtempSync(path.join(tmpdir(), 'coqcp-old-config-'))
  try {
    const filename = path.join(directory, 'config.json')
    writeFileSync(filename, JSON.stringify({ type: 'blockchain', inputs: [] }))
    const result = spawnSync(process.execPath, [cli, '?json', filename], {
      encoding: 'utf8',
    })
    expect(result.status).toBe(1)
    expect(result.stdout).toContain('Unrecognized type')
  } finally {
    rmSync(directory, { recursive: true, force: true })
  }
})
