import { CoqCPAST, ValueType } from './parse'

const getCoqString = (text: string): string => {
  const encoder = new TextEncoder()

  function getByteCode(string) {
    const utf8Bytes = encoder.encode(string)
    return Array.from(utf8Bytes).map(
      (byte) => `"${byte.toString().padStart(3, '0')}"`
    )
  }

  function constructCoqString(byteCode) {
    return byteCode.reduceRight(
      (acc, code) => `String ${code} (${acc})`,
      'EmptyString'
    )
  }

  const byteCode = getByteCode(text)
  const coqString = constructCoqString(byteCode)

  return coqString
}

const indent = '  '

const sanitizeName = (name: string): string =>
  [...name].filter((x) => /[0-9a-zA-Z'_]/.test(x)).join('')

export const coqCodegen = ({ environment, procedures }: CoqCPAST): string => {
  const procedureNameMap = new Map<string, number>()
  const sanitizedProcedureNameCollisions = new Map<string, number>()

  const preamble =
    'From CoqCP Require Import Options Imperative.\nFrom stdpp Require Import numbers list strings.\nOpen Scope type_scope.\n'

  const environmentCode = (() => {
    if (environment === null) {
      return `Definition environment : Environment := {| arrayType := fun _ => False; arrays := fun _ => [] |}.`
    }
    const arrayTypeFunction =
      'fun name => ' +
      [...environment.arrays.entries()]
        .map(([name, { itemTypes }]) => {
          const coqType = itemTypes
            .map((x) => (x === 'bool' ? 'bool' : 'Z'))
            .join(' * ')
          return `if decide (name = ${getCoqString(
            name
          )}) then ${coqType} else `
        })
        .join('') +
      'False'
    const arrayFunction =
      'fun name => ltac:(' +
      [...environment.arrays.entries()]
        .map(
          ([
            name,
            {
              itemTypes,
              length: { raw: rawLength },
            },
          ]) => {
            const value =
              '(' +
              itemTypes
                .map((x) => (x === 'bool' ? 'false' : '0%Z'))
                .join(', ') +
              ')'
            const list = 'repeat ' + value + ' ' + rawLength
            return `destruct (decide (name = ${getCoqString(
              name
            )})) as [h |]; [(rewrite h; simpl; exact (repeat ${value} ${rawLength})) |]; `
          }
        )
        .join('') +
      'exact [])'
    return `Definition environment : Environment := {| arrayType := ${arrayTypeFunction}; arrays := ${arrayFunction} |}.
`
  })()

  return preamble + environmentCode
}
