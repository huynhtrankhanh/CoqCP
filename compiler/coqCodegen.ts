import { PairMap } from './PairMap'
import { assert } from './assert'
import { CoqCPAST, PrimitiveType, ValueType } from './parse'
import { isNumeric } from './validateAST'

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

export const coqCodegen = (sortedModules: CoqCPAST[]): string => {
  const mapToSanitized = new PairMap<string, string, string>()
  const sanitizedProcedureNameCollisions = new Map<string, number>()

  const sanitize = (moduleName: string, procedureName: string) => {
    const existing = mapToSanitized.get([moduleName, procedureName])
    if (existing !== undefined) return existing
    const sanePart = sanitizeName(moduleName + "_" + procedureName)
    const discriminator = (() => {
      const count = sanitizedProcedureNameCollisions.get(sanePart) || 0
      sanitizedProcedureNameCollisions.set(sanePart, count + 1)
      return count
    })()
    const aggregate = 'funcdef_' + discriminator + '_' + sanePart
    mapToSanitized.set([moduleName, procedureName], aggregate)
    return aggregate
  }

  let code =
    'From CoqCP Require Import Options Imperative.\nFrom stdpp Require Import numbers list strings.\nRequire Import Coq.Strings.Ascii.\nOpen Scope type_scope.\n'

  for (const [moduleIndex, module] of sortedModules.entries()) {
    const { environment, procedures, moduleName } = module

    const environmentCode = (() => {
      if (environment === null || environment.arrays.size === 0) {
        return `Definition environment${moduleIndex} : Environment := {| arrayType := fun _ => False; arrays := fun _ => [] |}.
`
      }
      const arrayTypeFunction =
        'fun name => ' +
        [...environment.arrays.entries()]
          .map(([name, { itemTypes }]) => {
            const coqType =
              itemTypes.length === 0
                ? 'unit'
                : itemTypes.map((x) => (x === 'bool' ? 'bool' : 'Z')).join(' * ')
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
                itemTypes.length === 0
                  ? 'tt'
                  : '(' +
                  itemTypes
                    .map((x) => (x === 'bool' ? 'false' : '0%Z'))
                    .join(', ') +
                  ')'
              return `destruct (decide (name = ${getCoqString(
                name
              )})) as [h |]; [(rewrite h; simpl; exact (repeat ${value} ${rawLength})) |]; `
            }
          )
          .join('') +
        'exact [])'
      return `Definition environment${moduleIndex} : Environment := {| arrayType := ${arrayTypeFunction}; arrays := ${arrayFunction} |}.
`
    })()

    const decidableEquality = `#[export] Instance arrayTypeEqualityDecidable${moduleIndex} (name : string) : EqDecision (arrayType environment${moduleIndex} name).
Proof. simpl. repeat destruct (decide _). all: solve_decision. Defined.
`

    const generatedCodeForProcedures = procedures
      .map(({ body, name, variables }) => {
        const header =
          'Definition ' +
          sanitize(moduleName, name) +
          ` (bools : string -> bool) (numbers : string -> Z) : Action (WithArrays (arrayType environment${moduleIndex})) withArraysReturnValue unit := eliminateLocalVariables bools numbers `

        // every element of body is an Action returning absolutely anything
        const statements = body.map((statement) => {
          type BinderInfo = { number: number; type: 'int8' | 'int64' }
          const localBinderMap = new Map<string, BinderInfo>()
          let binderCounter = 0
          const dfs = (
            value: ValueType
          ): {
            expression: string
            type: PrimitiveType | 'statement' | PrimitiveType[]
          } => {
            const getBitWidth = (
              type: 'int8' | 'int16' | 'int32' | 'int64'
            ): 8 | 16 | 32 | 64 => {
              switch (type) {
                case 'int8':
                  return 8
                case 'int16':
                  return 16
                case 'int32':
                  return 32
                case 'int64':
                  return 64
              }
            }

            const getTuple = (value: ValueType[]) => {
              let tuple =
                'Done _ _ _ (' +
                value.map((_, i) => 'tuple_element_' + i).join(', ') +
                ')'
              for (const [index, element] of value.entries()) {
                tuple = `(bind ${dfs(element).expression
                  } (fun tuple_element_${index} => ${tuple}))`
              }
              return tuple
            }

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
                  case 'subtract':
                  case 'multiply':
                  case 'mod':
                  case 'bitwise or':
                  case 'bitwise xor':
                  case 'bitwise and':
                  case 'shift left':
                  case 'shift right': {
                    assert(isNumeric(leftType))
                    assert(leftType === rightType)
                    const bitWidth = getBitWidth(leftType)
                    const functionName = ((): string => {
                      switch (value.operator) {
                        case 'add':
                          return 'addInt' + bitWidth
                        case 'subtract':
                          return 'subInt' + bitWidth
                        case 'multiply':
                          return 'multInt' + bitWidth
                        case 'mod':
                          return 'modIntUnsigned'
                        case 'bitwise and':
                          return 'andBits'
                        case 'bitwise or':
                          return 'orBits'
                        case 'bitwise xor':
                          return 'xorBits'
                        case 'shift left':
                          return 'shiftLeft ' + bitWidth
                        case 'shift right':
                          return 'shiftRight ' + bitWidth
                      }
                    })()
                    return {
                      expression: `(${functionName} ${leftExpression} ${rightExpression})`,
                      type: leftType,
                    }
                  }
                  case 'boolean and':
                    return {
                      expression:
                        '(shortCircuitAnd ' +
                        leftExpression +
                        ' ' +
                        rightExpression +
                        ')',
                      type: 'bool',
                    }
                  case 'boolean or':
                    return {
                      expression:
                        '(shortCircuitOr ' +
                        leftExpression +
                        ' ' +
                        rightExpression +
                        ')',
                      type: 'bool',
                    }
                  case 'equal':
                    return {
                      expression: `(bind ${leftExpression} (fun x => bind ${rightExpression} (fun y => Done _ _ _ (bool_decide (x = y)))))`,
                      type: 'bool',
                    }
                  case 'noteq':
                    return {
                      expression: `(bind ${leftExpression} (fun x => bind ${rightExpression} (fun y => Done _ _ _ (bool_decide (x <> y)))))`,
                      type: 'bool',
                    }
                }
                break
              }
              case 'divide': {
                const { type: leftType, expression: leftExpression } = dfs(
                  value.left
                )
                const { type: rightType, expression: rightExpression } = dfs(
                  value.right
                )
                assert(leftType === rightType)
                assert(isNumeric(leftType))
                return {
                  expression: `(divIntUnsigned ${leftExpression} ${rightExpression})`,
                  type: leftType,
                }
              }
              case 'sDivide': {
                const { type: leftType, expression: leftExpression } = dfs(
                  value.left
                )
                const { type: rightType, expression: rightExpression } = dfs(
                  value.right
                )
                assert(leftType === rightType)
                assert(isNumeric(leftType))
                const bitWidth = getBitWidth(leftType)
                return {
                  expression: `(divInt${bitWidth}Signed ${leftExpression} ${rightExpression})`,
                  type: leftType,
                }
              }
              case 'coerceInt8':
              case 'coerceInt16':
              case 'coerceInt32':
              case 'coerceInt64': {
                const { type, expression } = dfs(value.value)
                assert(isNumeric(type) || type === 'bool')
                if (type === 'bool') {
                  return { expression: `(coerceBool ${expression})`, type }
                }
                return {
                  expression: `(bind ${expression} (fun x => Done _ _ _ (${value.type} x)))`,
                  type: (() => {
                    switch (value.type) {
                      case 'coerceInt8':
                        return 'int8'
                      case 'coerceInt16':
                        return 'int16'
                      case 'coerceInt32':
                        return 'int32'
                      case 'coerceInt64':
                        return 'int64'
                    }
                  })(),
                }
              }
              case 'continue': {
                return { expression: `(Done _ _ _ KeepGoing)`, type: 'statement' }
              }
              case 'break': {
                return { expression: `(Done _ _ _ Stop)`, type: 'statement' }
              }
              case 'flush': {
                return {
                  expression: `(flush (arrayType environment${moduleIndex}))`,
                  type: 'statement',
                }
              }
              case 'readChar': {
                return {
                  expression: `(readChar (arrayType environment${moduleIndex}))`,
                  type: 'int8',
                }
              }
              case 'writeChar': {
                const { expression } = dfs(value.value)
                return {
                  expression: `(bind ${expression} (fun x => writeChar (arrayType environment${moduleIndex}) x))`,
                  type: 'statement',
                }
              }
              case 'get': {
                const variable = variables.get(value.name)
                assert(variable !== undefined)
                if (isNumeric(variable.type)) {
                  return {
                    expression: `(numberLocalGet (arrayType environment${moduleIndex}) (${getCoqString(
                      value.name
                    )}))`,
                    type: variable.type,
                  }
                }
                return {
                  expression: `(booleanLocalGet (arrayType environment${moduleIndex}) (${getCoqString(
                    value.name
                  )}))`,
                  type: variable.type,
                }
              }
              case 'set': {
                const variable = variables.get(value.name)
                assert(variable !== undefined)
                const { expression } = dfs(value.value)
                if (isNumeric(variable.type)) {
                  return {
                    expression: `(bind ${expression} (fun x => numberLocalSet (arrayType environment${moduleIndex}) (${getCoqString(
                      value.name
                    )}) x))`,
                    type: 'statement',
                  }
                }
                return {
                  expression: `(booleanLocalSet (arrayType environment${moduleIndex}) (${getCoqString(
                    value.name
                  )}) ${expression})`,
                  type: 'statement',
                }
              }
              case 'retrieve': {
                assert(environment !== null)
                const declaration = environment.arrays.get(value.name)
                assert(declaration !== undefined)
                const { expression: indexExpression } = dfs(value.index)
                return {
                  expression: `(let x := bind ${indexExpression} (fun x => retrieve (arrayType environment${moduleIndex}) (${getCoqString(
                    value.name
                  )}) x) in ltac:(simpl in *; exact x))`,
                  type: declaration.itemTypes,
                }
              }
              case 'store': {
                const { expression: indexExpression } = dfs(value.index)
                let tuple = getTuple(value.tuple)
                return {
                  expression: `(bind ${indexExpression} (fun x => bind ${tuple} (fun y => store (arrayType environment${moduleIndex}) (${getCoqString(
                    value.name
                  )}) x ltac:(simpl in *; exact y))))`,
                  type: 'statement',
                }
              }
              case 'less': {
                const { expression: leftExpression } = dfs(value.left)
                const { expression: rightExpression } = dfs(value.right)
                return {
                  expression: `(bind ${leftExpression} (fun a => bind ${rightExpression} (fun b => Done _ _ _ (bool_decide (Z.lt a b)))))`,
                  type: 'bool',
                }
              }
              case 'sLess': {
                const { expression: leftExpression, type: leftType } = dfs(
                  value.left
                )
                const { expression: rightExpression, type: rightType } = dfs(
                  value.right
                )
                assert(leftType === rightType)
                assert(isNumeric(leftType))
                const bitWidth = getBitWidth(leftType)
                const toSigned = 'toSigned' + bitWidth
                return {
                  expression: `(bind ${leftExpression} (fun a => bind ${rightExpression} (fun b => Done _ _ _ (bool_decide (Z.lt (${toSigned} a) (${toSigned} b))))))`,
                  type: 'bool',
                }
              }
              case 'unaryOp': {
                const { expression, type } = dfs(value.value)
                switch (value.operator) {
                  case 'bitwise not': {
                    assert(isNumeric(type))
                    const bitWidth = getBitWidth(type)
                    return {
                      expression: `(notBits ${bitWidth} ${expression})`,
                      type,
                    }
                  }
                  case 'boolean not': {
                    return {
                      expression: `(bind ${expression} (fun x => Done _ _ _ (negb x)))`,
                      type,
                    }
                  }
                  case 'plus': {
                    return { expression, type }
                  }
                  case 'minus': {
                    return {
                      expression: `(bind ${expression} (fun x => -x))`,
                      type,
                    }
                  }
                }
              }
              case 'literal': {
                switch (value.valueType) {
                  case 'boolean': {
                    return {
                      expression: `(Done _ _ _ ${value.raw})`,
                      type: 'bool',
                    }
                  }
                  case 'number': {
                    const number = BigInt(value.raw)
                    const converted = number < 0n ? 2n ** 64n + number : number
                    return {
                      expression: `(Done _ _ _ ${converted}%Z)`,
                      type: 'int64',
                    }
                  }
                  case 'string':
                    assert(false, 'only makes sense within range()')
                }
              }
              case 'subscript': {
                const { expression, type } = dfs(value.value)
                assert(Array.isArray(type))
                const length = type.length
                const index = Number(value.index.raw)
                // because of validation, this is nonnegative and less than length
                if (type.length === 1) return { expression, type: type[0] }
                const reverseIndex = length - index - 1
                let finalExpression = expression
                for (let i = 0; i < reverseIndex; i++)
                  finalExpression = 'fst (' + finalExpression + ')'
                finalExpression = `(snd (${finalExpression}))`
                return { expression: finalExpression, type: type[index] }
              }
              case 'call': {
                const { presetVariables, procedure } = value
                let numberMap = '(Done _ _ _ (fun x => 0%Z))'
                let booleanMap = '(Done _ _ _ (fun x => false))'
                for (const [name, value] of presetVariables.entries()) {
                  const { expression, type } = dfs(value)
                  assert(isNumeric(type) || type === 'bool')
                  if (isNumeric(type)) {
                    numberMap = `(bind ${numberMap} (fun x => bind ${expression} (fun y => Done _ _ _ (update x (${getCoqString(
                      name
                    )}) y))))`
                  } else {
                    booleanMap = `(bind ${booleanMap} (fun x => bind ${expression} (fun y => Done _ _ _ (update x (${getCoqString(
                      name
                    )}) y))))`
                  }
                }
                return {
                  expression: `(bind ${numberMap} (fun x => bind ${booleanMap} (fun y => liftToWithLocalVariables (${sanitize(
                    moduleName, procedure
                  )} y x))))`,
                  type: 'statement',
                }
              }
              case 'condition': {
                const { condition, body, alternate } = value
                const { expression: conditionExpression } = dfs(condition)
                const bodyExpression = joinStatements(
                  body.map(dfs).map((x) => x.expression)
                )
                const alternateExpression = joinStatements(
                  alternate.map(dfs).map((x) => x.expression)
                )
                return {
                  expression: `(bind ${conditionExpression} (fun x => if x then ${bodyExpression} else ${alternateExpression}))`,
                  type: 'statement',
                }
              }
              case 'local binder': {
                const { name } = value
                const binder = localBinderMap.get(name)
                assert(binder !== undefined)
                return {
                  expression: 'binder_' + binder.number,
                  type: binder.type,
                }
              }
              case 'range': {
                const { loopVariable, loopBody, end } = value
                const previousBinderValue = localBinderMap.get(loopVariable)

                if (end.type === 'literal' && end.valueType === 'string')
                  localBinderMap.set(loopVariable, {
                    type: 'int8',
                    number: binderCounter++,
                  })
                else
                  localBinderMap.set(loopVariable, {
                    type: 'int64',
                    number: binderCounter++,
                  })

                const bodyExpression = joinStatements(
                  loopBody.map(dfs).map((x) => x.expression)
                )

                if (previousBinderValue === undefined) localBinderMap.delete(name)
                else localBinderMap.set(loopVariable, previousBinderValue)
                binderCounter--

                if (end.type === 'literal' && end.valueType === 'string') {
                  return {
                    expression: `(loopString (${getCoqString(
                      end.raw
                    )}) (fun binder_${binderCounter}_intermediate => let binder_${binderCounter} := Done _ _ _ binder_${binderCounter}_intermediate in bind (${bodyExpression}) (fun ignored => Done _ _ _ KeepGoing)))`,
                    type: 'statement',
                  }
                } else {
                  return {
                    expression: `(bind ${dfs(end).expression
                      } (fun x => loop (Z.to_nat x) (fun binder_${binderCounter}_intermediate => let binder_${binderCounter} := Done _ _ _ (Z.sub (Z.sub x (Z.of_nat binder_${binderCounter}_intermediate)) 1%Z) in bind (${bodyExpression}) (fun ignored => Done _ _ _ KeepGoing))))`,
                    type: 'statement',
                  }
                }
              }
              case 'cross module call': {
                const { arrayMapping, module: foreignModule, presetVariables, procedure } = value
                let numberMap = '(Done _ _ _ (fun x => 0%Z))'
                let booleanMap = '(Done _ _ _ (fun x => false))'
                for (const [name, value] of presetVariables.entries()) {
                  const { expression, type } = dfs(value)
                  assert(isNumeric(type) || type === 'bool')
                  if (isNumeric(type)) {
                    numberMap = `(bind ${numberMap} (fun x => bind ${expression} (fun y => Done _ _ _ (update x (${getCoqString(
                      name
                    )}) y))))`
                  } else {
                    booleanMap = `(bind ${booleanMap} (fun x => bind ${expression} (fun y => Done _ _ _ (update x (${getCoqString(
                      name
                    )}) y))))`
                  }
                }
                const { arrayMappingText, congruence } = (() => {
                  if (environment === null || environment.arrays.size === 0) return {
                    arrayMappingText: "(fun name => \"\")",
                    congruence: "ltac:(intro name; easy)"
                  }
                  const nonexistentArray = (() => {
                    const maxLength = [...environment.arrays.keys()].map(x => x.length).reduce((a, b) => Math.max(a, b))
                    return "a".repeat(maxLength + 1)
                  })()
                  const arrayMappingText = "(fun name => " + [...arrayMapping.entries()].map(([inForeign, inCurrent]) => `if (decide (name = ${getCoqString(inForeign)})) then ${getCoqString(inCurrent)} else `).join("") + JSON.stringify(nonexistentArray) + ")"
                  const congruence = "(fun name => ltac:(simpl; repeat case_decide; easy))"
                  return { arrayMappingText, congruence }
                }
                )()
                return {
                  expression: `(bind ${numberMap} (fun x => bind ${booleanMap} (fun y => liftToWithLocalVariables (translateArrays (${sanitize(
                    foreignModule, procedure
                  )} y x) (arrayType environment${moduleIndex}) ${arrayMappingText} ${congruence}))))`,
                  type: 'statement',
                }
              }
            }
          }
          return dfs(statement).expression
        })

        return (
          header +
          '(bind (' +
          joinStatements(statements) +
          ') (fun ignored => Done _ _ _ tt)).\n'
        )

        function joinStatements(statements: string[]) {
          if (statements.length === 0) return 'Done _ _ _ tt'
          return statements.reduce(
            (accumulated, current) =>
              'bind (' + accumulated + ') (fun ignored => ' + current + ')'
          )
        }
      })
      .join('')

    code += (
      environmentCode + decidableEquality + generatedCodeForProcedures
    )
  }
  return code
}
