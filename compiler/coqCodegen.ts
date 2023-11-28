import { assert } from './assert'
import { CoqCPAST, PrimitiveType, ValueType } from './parse'

const getCoqString = (text: string): string => {
  const encoder = new TextEncoder()

  function getByteCode(string: string) {
    const utf8Bytes = encoder.encode(string)
    return Array.from(utf8Bytes).map(
      (byte) => `"${byte.toString().padStart(3, '0')}"`
    )
  }

  function constructCoqString(byteCode: string[]) {
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
  const mapToSanitized = new Map<string, string>()
  const sanitizedProcedureNameCollisions = new Map<string, number>()

  const sanitize = (name: string) => {
    const existing = mapToSanitized.get(name)
    if (existing !== undefined) return existing
    const sanePart = sanitizeName(name)
    const discriminator = (() => {
      const count = sanitizedProcedureNameCollisions.get(sanePart) || 0
      sanitizedProcedureNameCollisions.set(sanePart, count + 1)
      return count
    })()
    const aggregate = '_$' + sanePart + '$' + discriminator
    mapToSanitized.set(name, aggregate)
    return aggregate
  }

  const preamble =
    'From CoqCP Require Import Options Imperative.\nFrom stdpp Require Import numbers list strings.\nRequire Import Coq.Strings.Ascii.\nOpen Scope type_scope.\n'

  const environmentCode = (() => {
    if (environment === null) {
      return `Definition environment : Environment := {| arrayType := fun _ => False; arrays := fun _ => [] |}.
`
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

  const decidableEquality = `#[export] Instance arrayTypeEqualityDecidable (name : string) : EqDecision (arrayType environment name).
Proof. simpl. repeat destruct (decide _). all: solve_decision. Defined.
`

  const generatedCodeForProcedures = procedures
    .map(({ body, name, variables }) => {
      const header =
        'Definition ' +
        sanitize(name) +
        ' arrayType (bools : string -> name) (numbers : string -> Z) : Action (BasicEffect (arrayType environment)) basicEffectReturnValue returnType := '

      // every element of body is an Action returning unit
      const statements = body.map((statement) => {
        const dfs = (
          value: ValueType
        ): { expression: string; type: PrimitiveType | PrimitiveType[] } => {
          switch (value.type) {
            case 'binaryOp': {
              const { expression: leftExpression, type: leftType } = dfs(
                value.left
              )
              const { expression: rightExpression, type: rightType } = dfs(
                value.right
              )
              assert(!Array.isArray(leftType))
              assert(!Array.isArray(rightType))
              switch (value.operator) {
                case 'add':
                  const xxx = leftType
              }
              break
            }
          }
        }
      })

      if (statements.length === 0) {
        return header + 'Done _ _ _ tt.\n'
      }

      return (
        header +
        statements.reduce(
          (accumulated, current) =>
            'bind (' + accumulated + ') (fun ignored => ' + current + ')'
        ) +
        '\n'
      )
    })
    .join('')

  return (
    preamble + environmentCode + decidableEquality + generatedCodeForProcedures
  )
}
