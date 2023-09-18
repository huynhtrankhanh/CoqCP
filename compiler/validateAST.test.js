// @ts-check
import { CoqCPASTTransformer, ParseError } from './parse'
import { validateAST } from './validateAST'
import { consumeNever } from './consumeNever'
/**
 * @param {string} code
 * @returns {import("./combinedError").CombinedError}
 */
const getCombinedError = (code) => {
  const parser = new CoqCPASTTransformer(code)
  try {
    var transformed = parser.transform()
  } catch (error) {
    if (!(error instanceof ParseError) && !(error instanceof SyntaxError))
      throw error
    return { type: 'parse error', message: error.message }
  }
  return { type: 'validation error', errors: validateAST(transformed) }
}

/**
 * @param {string} code
 * @returns {boolean}
 */
const noErrors = (code) => {
  const error = getCombinedError(code)
  if (error.type === 'parse error') return false
  if (error.type === 'validation error') return error.errors.length === 0
  return consumeNever(error)
}

/**
 * @param {string} code
 * @returns {boolean}
 */
const hasValidationErrorsOnly = (code) => {
  const error = getCombinedError(code)
  if (error.type === 'parse error') return false
  if (error.type === 'validation error') return error.errors.length !== 0
  return consumeNever(error)
}

/**
 * @param {string} code
 * @returns {boolean}
 */
const hasParseErrorsOnly = code => {
  const error = getCombinedError(code)
  return error.type === "parse error"
}

describe('validateAST', () => {
  it('accepts valid code', () => {
    const programs = [
      `environment({})`,
      `environment({ fib: array([int32], 0)})`,
      `environment({ intricate: array([bool, int64], 1) })`,
      `procedure("empty", {}, () => {})`,
      `environment({ a: array([int32], 1) })
procedure("hello", { a: bool }, () => {
  store("a", 0, [get("a")])
  set("a", retrieve("a", 0)[0])
})`,
    ]
    for (const program of programs) {
      if (!noErrors(program)) {
        console.log('failing program:', program)
        console.log('error:', getCombinedError(program))
        expect(false).toBe(true)
      }
    }
  })
  it('rejects invalid code (validate error)', () => {
    const programs = [
      `environment({ fractionalLength: array([int64], 10.5) })`
    ]
    for (const program of programs) {
      if (!hasValidationErrorsOnly(program)) {
        console.log('failing program:', program)
        console.log('error:', getCombinedError(program))
        expect(false).toBe(true)
      }
    }
  })
  it("rejects invalid code (parse error)", () => {
    const programs = [
    ]
    for (const program of programs) {
      if (!hasParseErrorsOnly(program)) {
        console.log('failing program:', program)
        console.log('error:', getCombinedError(program))
        expect(false).toBe(true)
      }
    }
  })
})
