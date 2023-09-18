// @ts-check
import { CoqCPASTTransformer, ParseError } from './parse'
import { validateAST } from './validateAST'
import { consumeNever } from "./consumeNever"
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
  if (error.type === "parse error") return false
  if (error.type === "validation error") return error.errors.length === 0
  return consumeNever(error.type)
}

/**
  * @param {string} code
  * @returns {boolean}
  */
const hasValidationErrorsOnly = (code) => {
  const error = getCombinedError(code)
  if (error.type === "parse error") return false
  if (error.type === "validation error") return error.errors.length !== 0
  return consumeNever(error.type)
}
