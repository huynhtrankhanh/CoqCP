import { CoqCPAST } from './parse'

export const solidityCodegen = (sortedModules: CoqCPAST[]): string => {
  const crossModuleProcedureMap = new PairMap<string, string, Procedure>()
  const procedureNameMap = new PairMap<string, string, number>()
  const seenModules = new Map<string, CoqCPAST>()
  const mainModule = sortedModules.find((x) => x.moduleName === '')

  let joined =
    '// SPDX-License-Identifier: UNLICENSED\ncontract GeneratedCode {\n'

  for (const module of sortedModules) {
  }

  joined += '}\n'

  return joined
}
