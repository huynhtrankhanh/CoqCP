import { CoqCPAST, ValueType } from './parse'

const indent = '  '

const sanitizeName = (name: string): string =>
  [...name].filter((x) => /[0-9a-zA-Z'_]/.test(x)).join('')

export const coqCodegen = ({ environment, procedures }: CoqCPAST): string => {
  const procedureNameMap = new Map<string, number>()
  const sanitizedProcedureNameCollisions = new Map<string, number>()

  const preamble = 'From CoqCP Require Import Options Imperative.\n'

  const environmentCode = (() => {
    if (environment === null) {
      return `Definition environment : Environment := {| arrayType := fun _ => False; arrays := fun _ => [] |}.`
    }
    for (const [name, array] of environment.arrays) {
    }
  })()
}
