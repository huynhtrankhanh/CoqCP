// @ts-check
import { CoqCPAST, ParseError } from './parse'
import { findDependencies } from './dependencyGraph'
import { sortModules } from './dependencyGraph'

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
    .map((x) => x.dependencyName)
    .sort()
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
    .map((x) => x.dependencyName)
    .sort()
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
    .map((x) => x.dependencyName)
    .sort()
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
    .map((x) => x.dependencyName)
    .sort()
  expect(dependencies).toEqual(['module1', 'module2'])
})

/**
 * Represents a CoqCPAST module.
 * @typedef {import('./parse').CoqCPAST} CoqCPAST
 */

/**
 * Test for sorting modules.
 */
describe('sortModules', () => {
  it('should process module with no dependencies first', () => {
    const moduleA = createEdges('A', [])
    const moduleB = createEdges('B', ['A'])
    const moduleC = createEdges('C', ['A', 'B'])
    const modules = [moduleC, moduleB, moduleA]
    const sortedModules = sortModules(modules)
    expect(sortedModules[0].moduleName).toBe('A')
  })

  it('should handle cyclic dependencies gracefully', () => {
    const moduleA = createEdges('A', ['B'])
    const moduleB = createEdges('B', ['A'])
    const modules = [moduleA, moduleB]
    const sortedModules = sortModules(modules)
    // Verify that the result is not in a cyclic order
    expect(sortedModules[0].moduleName).not.toBe('A')
    expect(sortedModules[1].moduleName).not.toBe('B')
  })

  it('should process modules with shared dependencies correctly', () => {
    const moduleA = createEdges('A', [])
    const moduleB = createEdges('B', ['A'])
    const moduleC = createEdges('C', ['A'])
    const modules = [moduleB, moduleC, moduleA]
    const sortedModules = sortModules(modules)
    // Verify that modules with shared dependencies are processed correctly
    expect(sortedModules[0].moduleName).toBe('A')
    expect(sortedModules[1].moduleName).toBe('B')
    expect(sortedModules[2].moduleName).toBe('C')
  })

  it('should process modules in correct order', () => {
    const moduleA = createEdges('A', [])
    const moduleB = createEdges('B', ['A'])
    const moduleC = createEdges('C', ['B'])
    const modules = [moduleC, moduleB, moduleA]
    const sortedModules = sortModules(modules)
    // Verify that modules are processed in the correct order
    expect(sortedModules[0].moduleName).toBe('A')
    expect(sortedModules[1].moduleName).toBe('B')
    expect(sortedModules[2].moduleName).toBe('C')
  })

  it('should handle empty input', () => {
    const modules = []
    const sortedModules = sortModules(modules)
    expect(sortedModules.length).toBe(0)
  })

  it('should handle single module input', () => {
    const moduleA = createEdges('A', [])
    const modules = [moduleA]
    const sortedModules = sortModules(modules)
    expect(sortedModules.length).toBe(1)
    expect(sortedModules[0].moduleName).toBe('A')
  })
})
