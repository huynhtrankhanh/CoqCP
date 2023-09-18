// @ts-check
import { CoqCPASTTransformer, ParseError } from './parse'
import { validateAST } from './validateAST'
/**
 * @param {string} code
 * @returns {import("./combinedError").CombinedError}
 */
const combined = (code) => {
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
