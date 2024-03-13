// @ts-check
import { createEdges } from './dependencyGraph.test'
import { validateAST } from './validateAST'

describe('validateAST', () => {
  test('No cyclic dependencies', () => {
    // Create multiple ASTs without cyclic dependencies
    const modules = [
      createEdges('module1', []),
      createEdges('module2', ['module1']),
      createEdges('module3', ['module1', 'module2']),
    ]

    // Validate ASTs
    const errors = validateAST(modules)

    // Check if the returned value is an empty array
    expect(errors).toEqual([])
  })

  test('With cyclic dependencies', () => {
    // Create multiple ASTs with cyclic dependencies
    const modules = [
      createEdges('module1', ['module2']),
      createEdges('module2', ['module3']),
      createEdges('module3', ['module1']),
    ]

    // Validate ASTs
    const errors = validateAST(modules)

    // Check if returned value is NOT EMPTY and every error has type "call implicated in cycle"
    expect(errors).not.toEqual([])
    console.log(errors)
    expect(
      errors.every((error) => error.type === 'call implicated in cycle')
    ).toBe(true)
  })
})
