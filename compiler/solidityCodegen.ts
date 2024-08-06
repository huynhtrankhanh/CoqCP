import { CoqCPAST } from './parse'

export const solidityCodegen = (sortedModules: CoqCPAST[]): string => {
  let joined =
    '// SPDX-License-Identifier: UNLICENSED\ncontract GeneratedCode {\n'

  for (const module of sortedModules) {
  }

  joined += '}\n'

  return joined
}
