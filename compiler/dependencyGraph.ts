import { consumeNever } from './consumeNever'
import { findCycle } from './findCycle'
import { CoqCPAST, ValueType, Location } from './parse'
import { topologicalSort } from './topologicalSort'
import { ValidationError } from './validateAST'

// There might be duplicate dependencies
export const findDependencies = ({ procedures }: CoqCPAST) => {
  function findDependencies(valueType: ValueType): void {
    switch (valueType.type) {
      case 'local binder':
        // Local binders do not introduce dependencies
        break
      case 'literal':
        // Literals do not introduce dependencies
        break
      case 'binaryOp':
        findDependencies(valueType.left)
        findDependencies(valueType.right)
        break
      case 'unaryOp':
        findDependencies(valueType.value)
        break
      case 'get':
        // Getting a variable does not introduce dependencies
        break
      case 'set':
        findDependencies(valueType.value)
        break
      case 'store':
        findDependencies(valueType.index)
        valueType.tuple.forEach((value) => findDependencies(value))
        break
      case 'retrieve':
        findDependencies(valueType.index)
        break
      case 'range':
        findDependencies(valueType.end)
        valueType.loopBody.forEach((instruction) =>
          findDependencies(instruction)
        )
        break
      case 'writeChar':
        findDependencies(valueType.value)
        break
      case 'subscript':
        findDependencies(valueType.value)
        break
      case 'condition':
        findDependencies(valueType.condition)
        valueType.body.forEach((instruction) => findDependencies(instruction))
        valueType.alternate.forEach((instruction) =>
          findDependencies(instruction)
        )
        break
      case 'sDivide':
      case 'divide':
      case 'less':
      case 'sLess':
        findDependencies(valueType.left)
        findDependencies(valueType.right)
        break
      case 'coerceInt8':
      case 'coerceInt16':
      case 'coerceInt32':
      case 'coerceInt64':
        findDependencies(valueType.value)
        break
      case 'call':
        valueType.presetVariables.forEach((value) => findDependencies(value))
        break
      case 'cross module call':
        dependencies.push({
          dependencyName: valueType.module,
          mention: valueType.location,
        })
        valueType.presetVariables.forEach((value) => findDependencies(value))
        break
      case 'break':
      case 'continue':
      case 'flush':
      case 'readChar':
        // These instructions do not introduce dependencies
        break
      default:
        consumeNever(valueType)
    }
  }

  type DependencyMention = { dependencyName: string; mention: Location }

  const dependencies: DependencyMention[] = []
  for (const procedure of procedures) {
    for (const instruction of procedure.body) {
      findDependencies(instruction)
    }
  }
  return dependencies
}

export const createEdgeIndexMap = () => {
  const map = new Map()

  return {
    set(key: [number, number], value: number) {
      map.set(JSON.stringify(key), value)
    },
    get(key: [number, number]) {
      return map.get(JSON.stringify(key))
    },
  }
}

export const createEdgeListAndMentionLocation = (
  modules: CoqCPAST[],
  indexMap: Map<string, number>
) => {
  const edgeList: [number, number][] = []
  const mentionLocation: Location[] = []

  for (const [toNumber, module] of modules.entries()) {
    const dependencies = findDependencies(module).filter(
      (x) => x.dependencyName !== module.moduleName
    )
    for (const { dependencyName, mention } of dependencies) {
      const fromNumber = indexMap.get(dependencyName)
      if (fromNumber === undefined) continue
      edgeList.push([fromNumber, toNumber])
      mentionLocation.push(mention)
    }
  }

  return { edgeList, mentionLocation }
}

export const createIndexMap = (modules: CoqCPAST[]) => {
  const indexMap = new Map()

  const existingModuleNames = modules.map((x) => x.moduleName)
  for (const [index, name] of existingModuleNames.entries()) {
    indexMap.set(name, index)
  }

  return indexMap
}

export const validateCyclicDependencies = (modules: CoqCPAST[]) => {
  const indexMap = createIndexMap(modules)
  const { edgeList, mentionLocation } = createEdgeListAndMentionLocation(
    modules,
    indexMap
  )
  const edgeIndexMap = createEdgeIndexMap()

  for (const [index, edge] of edgeList.entries()) {
    edgeIndexMap.set(edge, index)
  }

  const cycle = findCycle(edgeList)

  if (cycle === undefined) return []

  if (cycle.length < 3) {
    throw new Error(
      "Cycle with length less than 3 - can't happen. This is a compiler bug."
    )
  }

  const errors: ValidationError[] = []
  for (let i = 0; i + 1 < cycle.length; i++) {
    const edgeIndex = edgeIndexMap.get([cycle[0], cycle[1]])!
    const mention = mentionLocation[edgeIndex]
    errors.push({
      type: 'call implicated in cycle',
      location: { ...mention, moduleName: modules[cycle[1]].moduleName },
    })
  }

  return errors
}

export function sortModules(modules: CoqCPAST[]): CoqCPAST[] {
  // Step 1: Create index map
  const indexMap = createIndexMap(modules)

  // Step 2: Create edge list and mention location
  const { edgeList } = createEdgeListAndMentionLocation(modules, indexMap)

  // Step 3: Perform topological sort
  const sortedIndices = topologicalSort(modules.length, edgeList)

  // Step 4: Rearrange modules according to sorted indices
  const sortedModules = sortedIndices.map((index) => modules[index])

  return sortedModules
}
