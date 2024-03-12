// @ts-check
import { CoqCPAST, ParseError } from './parse'
import { findDependencies } from './dependencyGraph'

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

/**
 * Tests for the findDependencies function
 */

/**
 * Test case when CoqCPAST has no procedures
 */
test('No procedures in CoqCPAST', () => {
  const x = new CoqCPAST()
  const dependencies = findDependencies(x)
  expect(dependencies).toEqual([])
})

/**
 * Test case when CoqCPAST has procedures with no cross module calls
 */
test('Procedures with no cross module calls', () => {
  /**
   * @type {import("./parse").Procedure}
   */
  const procedure1 = {
    name: 'procedure1',
    variables: new Map(),
    body: [
      {
        type: 'set',
        name: 'x',
        value: {
          type: 'literal',
          valueType: 'number',
          raw: '42',
          location: {
            start: { line: 1, column: 0 },
            end: { line: 1, column: 2 },
          },
        },
        location: {
          start: { line: 1, column: 0 },
          end: { line: 1, column: 2 },
        },
      },
    ],
  }
  /**
   * @type {import("./parse").Procedure}
   */
  const procedure2 = {
    name: 'procedure2',
    variables: new Map(),
    body: [
      {
        type: 'get',
        name: 'x',
        location: {
          start: { line: 1, column: 0 },
          end: { line: 1, column: 2 },
        },
      },
    ],
  }
  const x = new CoqCPAST()
  x.procedures = [procedure1, procedure2]
  const dependencies = findDependencies(x)
  expect(dependencies).toEqual([])
})

/**
 * Test case when CoqCPAST has procedures with cross module calls
 */
test('Procedures with cross module calls', () => {
  /**
   * @type {import("./parse").Procedure}
   */
  const procedure1 = {
    name: 'procedure1',
    variables: new Map(),
    body: [
      {
        type: 'cross module call',
        procedure: 'proc2',
        module: 'module2',
        presetVariables: new Map(),
        arrayMapping: new Map(),
        location: {
          start: { line: 1, column: 0 },
          end: { line: 1, column: 2 },
        },
      },
    ],
  }
  /**
   * @type {import("./parse").Procedure}
   */
  const procedure2 = {
    name: 'procedure2',
    variables: new Map(),
    body: [
      {
        type: 'get',
        name: 'x',
        location: {
          start: { line: 1, column: 0 },
          end: { line: 1, column: 2 },
        },
      },
    ],
  }
  const x = new CoqCPAST()
  x.procedures = [procedure1, procedure2]
  const dependencies = findDependencies(x)
  expect(dependencies).toEqual(['module2'])
})

/**
 * Test case when CoqCPAST has circular dependencies
 */
test('Circular dependencies in CoqCPAST', () => {
  /**
   * @type {import("./parse").Procedure}
   */
  const procedure1 = {
    name: 'procedure1',
    variables: new Map(),
    body: [
      {
        type: 'cross module call',
        procedure: 'proc2',
        module: 'module2',
        presetVariables: new Map(),
        arrayMapping: new Map(),
        location: {
          start: { line: 1, column: 0 },
          end: { line: 1, column: 2 },
        },
      },
    ],
  }
  /**
   * @type {import("./parse").Procedure}
   */
  const procedure2 = {
    name: 'procedure2',
    variables: new Map(),
    body: [
      {
        type: 'cross module call',
        procedure: 'proc1',
        module: 'module1',
        presetVariables: new Map(),
        arrayMapping: new Map(),
        location: {
          start: { line: 1, column: 0 },
          end: { line: 1, column: 2 },
        },
      },
    ],
  }
  const x = new CoqCPAST()
  x.procedures = [procedure1, procedure2]
  const dependencies = findDependencies(x)
  expect(dependencies).toEqual(['module1', 'module2'])
})
