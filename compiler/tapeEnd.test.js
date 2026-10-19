import { mkdtempSync, rmSync, writeFileSync } from 'fs'
import { tmpdir } from 'os'
import path from 'path'
import { execFileSync, spawn } from 'child_process'
import { CoqCPASTTransformer } from './parse'
import { sortModules } from './dependencyGraph'
import { validateAST } from './validateAST'
import { cppCodegen } from './cppCodegen'
import { coqCodegen } from './coqCodegen'

const parse = (source) => new CoqCPASTTransformer(source).transform()
const modules = (source) => {
  const result = sortModules(
    (Array.isArray(source) ? source : [source]).map(parse)
  )
  expect(validateAST(result)).toEqual([])
  return result
}
const withCpp = async (source, check) => {
  const dir = mkdtempSync(path.join(tmpdir(), 'coqcp-tape-'))
  try {
    const cpp = path.join(dir, 'Main.cpp')
    const binary = path.join(dir, 'main')
    writeFileSync(cpp, cppCodegen(modules(source)))
    execFileSync('g++', ['-std=c++20', '-O1', cpp, '-o', binary])
    await check(binary)
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
}

test.each([
  'tapeEnd()',
  'tapeEnd(1)',
  'tapeEnd(x => x)',
  'tapeEnd(() => {})',
  'tapeEnd((x,y) => {})',
  'tapeEnd(({x}) => {})',
  'tapeEnd(async x => {})',
  'tapeEnd(x => {}, 1)',
])('rejects malformed callback: %s', (command) => {
  expect(() => parse(`procedure('main', {}, () => { ${command} })`)).toThrow()
})

test('validates lexical binders and limits loop control to loop bodies', () => {
  modules(`procedure('main', {x: int8}, () => {
    tapeEnd(c => { set('x', c); if (c == coerceInt8(0)) { ;('continue') }; ;('break') })
  })`)
  for (const body of [
    `tapeEnd(c => {}); set('x', c)`,
    `tapeEnd(c => {}); ;('break')`,
    `tapeEnd(c => {}); ;('continue')`,
    `set('x', tapeEnd(c => {}))`,
  ]) {
    expect(
      validateAST(
        sortModules([parse(`procedure('main', {x: int64}, () => { ${body} })`)])
      )
    ).not.toEqual([])
  }
})

test('does not expose the internal remaining-tape measure to IIL', () => {
  for (const expression of [
    'TapeRemaining()',
    'tapeRemaining()',
    'readTapeLength()',
  ]) {
    expect(() =>
      parse(`procedure('main', {x: int64}, () => { set('x', ${expression}) })`)
    ).toThrow()
  }
  const source = `procedure('main', {}, () => { tapeEnd(c => {}) })`
  const cpp = cppCodegen(modules(source))
  expect(cpp).not.toMatch(/TapeRemaining|tapeRemaining|fseek|lseek/)
  expect(cpp).toContain('!= UINT64_MAX')
})

test('tapeEnd binds int8 and requires explicit widening to int64', () => {
  modules(`procedure('main', {byte: int8, word: int64}, () => {
    tapeEnd(c => {
      writeChar(c)
      set('byte', c)
      set('word', coerceInt64(c))
    })
  })`)
  expect(
    validateAST(
      sortModules([
        parse(`procedure('main', {word: int64}, () => {
    tapeEnd(c => { set('word', c) })
  })`),
      ])
    )
  ).not.toEqual([])
})

test('break, continue and body reads share the same cursor', async () => {
  await withCpp(
    `procedure('main', {}, () => {
    tapeEnd(c => {
      if (c == coerceInt8(35)) { ;('continue') }
      if (c == coerceInt8(33)) { ;('break') }
      writeChar(coerceInt8(c))
      writeChar(coerceInt8(readChar()))
    })
    writeChar(coerceInt8(readChar()))
  })`,
    (binary) => {
      expect(execFileSync(binary, { input: 'aX#bY!Z', encoding: 'utf8' })).toBe(
        'aXbYZ'
      )
    }
  )
})

test('empty input and EOF reached inside a called procedure stop the loop', async () => {
  await withCpp(
    `procedure('consume', {}, () => { readChar() })
    procedure('main', {}, () => {
      tapeEnd(c => { writeChar(coerceInt8(c)); call('consume', {}) })
      if (readChar() == -1) { writeChar(coerceInt8(69)) }
    })`,
    (binary) => {
      expect(execFileSync(binary, { input: '', encoding: 'utf8' })).toBe('E')
      expect(execFileSync(binary, { input: 'abcd', encoding: 'utf8' })).toBe(
        'acE'
      )
      expect(execFileSync(binary, { input: 'abc', encoding: 'utf8' })).toBe(
        'acE'
      )
    }
  )
})

test('nested tape and range loops restore shadowed binders', async () => {
  await withCpp(
    `procedure('main', {}, () => {
    tapeEnd(c => {
      range(1, c => {
        tapeEnd(c => { writeChar(coerceInt8(c)); ;('break') })
        writeChar(coerceInt8(c + 48))
      })
      writeChar(coerceInt8(c))
      ;('break')
    })
    writeChar(coerceInt8(readChar()))
  })`,
    (binary) => {
      expect(execFileSync(binary, { input: 'ABC', encoding: 'utf8' })).toBe(
        'B0AC'
      )
    }
  )
})

test('finds foreign calls and transitive array growth inside tapeEnd', async () => {
  await withCpp(
    [
      `environment({data: array([int8], 0)})
     procedure('main', {}, () => {
       tapeEnd(c => {
         call(Leaf, {x: 'data'}, 'save', {value: coerceInt8(c)})
         writeChar(retrieve('data', 0)[0])
       })
     })`,
      `module(Leaf)
     environment({x: array([int8], 0)})
     procedure('save', {value: int8}, () => {
       grow('x', 1)
       store('x', 0, [get('value')])
     })`,
    ],
    (binary) => {
      expect(execFileSync(binary, { input: 'abc', encoding: 'utf8' })).toBe(
        'abc'
      )
    }
  )
})

test('a shadowing numeric loop evaluates its bound using the outer tape binder', async () => {
  await withCpp(
    `procedure('main', {}, () => {
    tapeEnd(c => {
      range(coerceInt64(c), c => { writeChar(coerceInt8(c + 48)) })
      ;('break')
    })
  })`,
    (binary) => {
      expect(
        execFileSync(binary, { input: Buffer.from([2]), encoding: 'utf8' })
      ).toBe('01')
    }
  )
})

test('preserves every byte across multiple input buffer refills', async () => {
  await withCpp(
    `procedure('main', {}, () => {
    tapeEnd(c => { writeChar(c) })
  })`,
    (binary) => {
      const input = Buffer.alloc(3 * (1 << 16) + 17)
      for (let i = 0; i < input.length; ++i) input[i] = i % 256
      expect(execFileSync(binary, { input, timeout: 3000 }).equals(input)).toBe(
        true
      )
    }
  )
})

test('flushes and breaks without waiting for EOF on an open pipe', async () => {
  await withCpp(
    `procedure('main', {}, () => {
    tapeEnd(c => {
      if (c == coerceInt8(10)) { ;('break') }
      writeChar(coerceInt8(c))
      ;('flush')
    })
  })`,
    async (binary) => {
      const child = spawn(binary, [], { stdio: ['pipe', 'pipe', 'pipe'] })
      try {
        const output = await new Promise((resolve, reject) => {
          let output = ''
          const timer = setTimeout(
            () => reject(new Error('Blocked waiting for EOF')),
            2000
          )
          child.on('error', (e) => {
            clearTimeout(timer)
            reject(e)
          })
          child.stdout.on('data', (data) => {
            output += data.toString()
          })
          child.on('close', (code) => {
            clearTimeout(timer)
            if (code === 0) resolve(output)
            else reject(new Error(`Exit ${code}`))
          })
          child.stdin.write('ok\n') // Deliberately leave stdin open.
        })
        expect(output).toBe('ok')
      } finally {
        if (child.exitCode === null) child.kill()
      }
    }
  )
})

test('generated Rocq executes the same break/continue and extra-read program', () => {
  const source = `procedure('main', {}, () => {
    tapeEnd(c => {
      if (c == coerceInt8(35)) { ;('continue') }
      if (c == coerceInt8(33)) { ;('break') }
      writeChar(coerceInt8(c))
      writeChar(coerceInt8(readChar()))
    })
    writeChar(coerceInt8(readChar()))
  })`
  const dir = mkdtempSync(path.join(tmpdir(), 'coqcp-tape-rocq-'))
  try {
    const file = path.join(dir, 'TapeProgram.v')
    writeFileSync(
      file,
      coqCodegen(modules(source)) +
        `
From CoqCP Require Import Execution.
Open Scope Z_scope.
Definition initial : @Machine arrayIndex0 (arrayType _ environment0) :=
  {| memory := arrays _ environment0; stdin := [97;88;35;98;89;33;90]; stdout := [] |}.
Example cursor_and_control :
  option_map (fun response => stdout (snd response))
    (exec (funcdef_0__main (fun x => match x with end) (fun x => match x with end)) initial)
    = Some [97;88;98;89;90].
Proof. vm_compute. reflexivity. Qed.
Print Assumptions cursor_and_control.
`
    )
    const result = execFileSync(
      '/opt/rocq/9.3.0/bin/rocq',
      [
        'compile',
        '-q',
        '-Q',
        path.resolve(__dirname, '../theories'),
        'CoqCP',
        file,
      ],
      { encoding: 'utf8' }
    )
    expect(result).toContain('Closed under the global context')
    expect(result).not.toContain('Axioms:')
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
}, 30000)
