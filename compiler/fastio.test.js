import fs from 'fs'
import os from 'os'
import path from 'path'
import { spawn, spawnSync } from 'child_process'
import { CoqCPASTTransformer } from './parse'
import { cppCodegen } from './cppCodegen'

it('reads a short interactive response while stdin stays open', async () => {
  const ast = new CoqCPASTTransformer(`
    procedure('main', {}, () => {
      range('! ', (c) => { writeChar(c) })
      range(4, (i) => { writeChar(coerceInt8(readChar())) })
      ;('flush')
    })
  `).transform()
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'coqcp-interactive-'))
  let child
  try {
    const source = path.join(directory, 'main.cpp')
    const binary = path.join(directory, 'main')
    fs.writeFileSync(source, cppCodegen([ast]))
    const compilation = spawnSync('g++', ['-std=c++20', source, '-o', binary])
    expect(compilation.status).toBe(0)
    child = spawn(binary, [], { stdio: ['pipe', 'pipe', 'pipe'] })
    const output = await new Promise((resolve, reject) => {
      let text = ''
      const timer = setTimeout(() => reject(new Error('Reader blocked with stdin open')), 2000)
      child.on('error', (error) => { clearTimeout(timer); reject(error) })
      child.stdout.on('data', (bytes) => { text += bytes.toString() })
      child.on('close', (code) => {
        clearTimeout(timer)
        if (code === 0) resolve(text)
        else reject(new Error(`Program exited with ${code}`))
      })
      // write() sends these bytes; end() is deliberately never called.
      child.stdin.write('3 1\n')
    })
    expect(output).toBe('! 3 1\n')
  } finally {
    if (child && child.exitCode === null) child.kill()
    fs.rmSync(directory, { recursive: true, force: true })
  }
})

it('preserves bytes across buffer refills and returns the EOF sentinel', () => {
  const size = 3 * (1 << 16) + 17
  const ast = new CoqCPASTTransformer(`
    procedure('main', {}, () => {
      range(${size}, (i) => { writeChar(coerceInt8(readChar())) })
      if (readChar() == -1) { writeChar(coerceInt8(69)) }
    })
  `).transform()
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'coqcp-fastio-'))
  try {
    const source = path.join(directory, 'main.cpp')
    const binary = path.join(directory, 'main')
    const input = Buffer.alloc(size)
    for (let i = 0; i < size; i++) input[i] = i % 256
    fs.writeFileSync(source, cppCodegen([ast]))
    const compilation = spawnSync('g++', ['-std=c++20', source, '-o', binary])
    expect(compilation.status).toBe(0)
    const expected = Buffer.concat([input, Buffer.from('E')])
    const piped = spawnSync(binary, [], { input, timeout: 2000 })
    expect(piped.status).toBe(0)
    expect(piped.stdout.equals(expected)).toBe(true)
    const inputFile = path.join(directory, 'input')
    fs.writeFileSync(inputFile, input)
    const fd = fs.openSync(inputFile, 'r')
    try {
      const fromFile = spawnSync(binary, [], { stdio: [fd, 'pipe', 'pipe'], timeout: 2000 })
      expect(fromFile.status).toBe(0)
      expect(fromFile.stdout.equals(expected)).toBe(true)
    } finally {
      fs.closeSync(fd)
    }
  } finally {
    fs.rmSync(directory, { recursive: true, force: true })
  }
})
