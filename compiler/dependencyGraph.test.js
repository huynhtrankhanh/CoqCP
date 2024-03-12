// @ts-check
import {
  CoqCPAST,
  ArrayDeclaration,
  Variable,
  ValueType,
  Instruction,
  Location,
  ParseError,
} from './parse'

/**
 * Creates a CoqCPAST object with the given moduleName and dependencies.
 * @param {string} moduleName - The name of the module.
 * @param {string[]} dependencies - An array of dependency module names.
 * @returns {CoqCPAST} The created CoqCPAST object.
 * @throws {ParseError} If any dependency is missing.
 */
function createEdges(moduleName, dependencies) {
  const coqCPAST = new CoqCPAST()
  coqCPAST.moduleName = moduleName
  coqCPAST.environment = {
    arrays: new Map(),
  }

  // Throw error if dependencies are missing
  for (const dependency of dependencies) {
    if (!dependency) {
      throw new ParseError('Dependency is missing')
    }
  }

  // Initialize procedures with cross module calls
  coqCPAST.procedures = dependencies.map((dep) => ({
    name: dep,
    variables: new Map(),
    body: [
      {
        type: 'cross module call',
        procedure: 'your_procedure_name',
        module: dep,
        presetVariables: new Map(),
        arrayMapping: new Map(),
        location: {
          start: { line: 0, column: 0 },
          end: { line: 0, column: 0 },
        },
      },
    ],
  }))

  return coqCPAST
}
