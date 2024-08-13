import { CoqCPAST } from './parse'

export const solidityCodegen = (sortedModules: CoqCPAST[]): string => {
  const mainModule = sortedModules.find((x) => x.moduleName === '')

  let joined =
    '// SPDX-License-Identifier: UNLICENSED\ncontract GeneratedCode {\n'

  for (const module of sortedModules) {
  }

  joined += '}\n'

  return joined
}
