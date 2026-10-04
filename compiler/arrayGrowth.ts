import { CoqCPAST, ValueType } from './parse'

// Array mappings alias storage, so both ends must use the same representation.
// Propagate growth through all mappings, including read-only helper modules.
export const analyzeArrayGrowth = (modules: CoqCPAST[]): Map<string, Set<string>> => {
  const growing = new Map(modules.map((module) => [module.moduleName, new Set<string>()]))
  const mappings: { caller: string; local: string; callee: string; foreign: string }[] = []

  const visit = (module: string, value: ValueType): void => {
    switch (value.type) {
      case 'grow':
        growing.get(module)!.add(value.name)
        visit(module, value.length)
        break
      case 'cross module call':
        for (const [foreign, local] of value.arrayMapping) {
          mappings.push({ caller: module, local, callee: value.module, foreign })
        }
        value.presetVariables.forEach((argument) => visit(module, argument))
        break
      case 'call':
        value.presetVariables.forEach((argument) => visit(module, argument))
        break
      case 'condition':
        visit(module, value.condition)
        value.body.forEach((instruction) => visit(module, instruction))
        value.alternate.forEach((instruction) => visit(module, instruction))
        break
      case 'range':
        visit(module, value.end)
        value.loopBody.forEach((instruction) => visit(module, instruction))
        break
      case 'store':
        visit(module, value.index)
        value.tuple.forEach((element) => visit(module, element))
        break
      case 'retrieve':
        visit(module, value.index)
        break
      case 'subscript':
        visit(module, value.value)
        visit(module, value.index)
        break
      case 'binaryOp':
      case 'divide':
      case 'sDivide':
      case 'less':
      case 'sLess':
        visit(module, value.left)
        visit(module, value.right)
        break
      case 'unaryOp':
      case 'set':
      case 'writeChar':
      case 'coerceInt8':
      case 'coerceInt16':
      case 'coerceInt32':
      case 'coerceInt64':
        visit(module, value.value)
        break
      case 'literal':
      case 'local binder':
      case 'get':
      case 'readChar':
      case 'break':
      case 'continue':
      case 'flush':
        break
    }
  }

  for (const module of modules) {
    for (const procedure of module.procedures) {
      procedure.body.forEach((instruction) => visit(module.moduleName, instruction))
    }
  }
  let changed = true
  while (changed) {
    changed = false
    for (const { caller, local, callee, foreign } of mappings) {
      const callerArrays = growing.get(caller)
      const calleeArrays = growing.get(callee)
      if (callerArrays === undefined || calleeArrays === undefined) continue
      if (callerArrays.has(local) || calleeArrays.has(foreign)) {
        if (!callerArrays.has(local) || !calleeArrays.has(foreign)) changed = true
        callerArrays.add(local)
        calleeArrays.add(foreign)
      }
    }
  }
  return growing
}
