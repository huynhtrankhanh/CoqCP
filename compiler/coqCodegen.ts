import { PairMap } from './PairMap'
import { assert } from './assert'
import { COMMUNICATION, CoqCPAST, PrimitiveType, ValueType } from './parse'
import { isNumeric } from './validateAST'

const getCoqString = (text: string): string => {
  const encoder = new TextEncoder()
  const utf8Bytes = encoder.encode(text)

  if (utf8Bytes.every((x) => x < 128)) {
    return '"' + text.split('"').join('""') + '"'
  }

  const byteCode = Array.from(utf8Bytes).map(
    (byte) => `"${byte.toString().padStart(3, '0')}"`
  )

  function constructCoqString(byteCode: string[]) {
    return byteCode.reduceRight(
      (acc, code) => `String ${code} (${acc})`,
      'EmptyString'
    )
  }

  const coqString = constructCoqString(byteCode)

  return coqString
}

const byteLength = (x: string) => {
  const encoder = new TextEncoder()
  const bytes = encoder.encode(x)
  return bytes.length
}

const indent = '  '

const generateInductive = (name: string, arms: string[]) => {
  if (arms.length === 0) return 'Inductive ' + name + ' : Type :=.\n'
  return (
    `Inductive ${name} :=` + '\n' + arms.map((x) => '| ' + x).join('\n') + '.\n'
  )
}

const sanitizeName = (name: string): string =>
  [...name].filter((x) => /[0-9a-zA-Z'_]/.test(x)).join('')

export const coqCodegen = (sortedModules: CoqCPAST[]): string => {
  const mapToSanitizedFunc = new PairMap<string, string, string>()
  const mapToSanitizedVar = new PairMap<string, string, string>()
  const mapToSanitizedArray = new PairMap<string, string, string>()

  const sanitizedFuncCollisions = new Map<string, number>()
  const sanitizedVarCollisions = new Map<string, number>()
  const sanitizedArrayCollisions = new Map<string, number>()

  const sanitize = (
    moduleName: string,
    identifier: string,
    namespace: 'funcdef' | 'vardef' | 'arraydef' | 'arrayidx',
    mapToSanitized: PairMap<string, string, string>,
    sanitizedIdentifierCollisions: Map<string, number>
  ) => {
    const existing = mapToSanitized.get([moduleName, identifier])
    if (existing !== undefined) return existing
    const sanePart = sanitizeName(moduleName + '_' + identifier)
    const discriminator = (() => {
      const count = sanitizedIdentifierCollisions.get(sanePart) || 0
      sanitizedIdentifierCollisions.set(sanePart, count + 1)
      return count
    })()
    const aggregate = namespace + '_' + discriminator + '_' + sanePart
    mapToSanitized.set([moduleName, identifier], aggregate)
    return aggregate
  }

  const sanitizeFunction = (moduleName: string, identifier: string) =>
    sanitize(
      moduleName,
      identifier,
      'funcdef',
      mapToSanitizedFunc,
      sanitizedFuncCollisions
    )

  const sanitizeVariable = (
    moduleName: string,
    functionName: string,
    identifier: string
  ) =>
    sanitize(
      moduleName,
      JSON.stringify([functionName, '_', identifier]),
      'vardef',
      mapToSanitizedVar,
      sanitizedVarCollisions
    )

  const sanitizeArray = (moduleName: string, identifier: string) =>
    sanitize(
      moduleName,
      identifier,
      'arraydef',
      mapToSanitizedArray,
      sanitizedArrayCollisions
    )

  const sanitizeVariableIndex = (
    moduleName: string,
    functionName: string
  ): string => 'vars' + sanitizeFunction(moduleName, functionName)

  let code =
    'From CoqCP Require Import Options Imperative.\nFrom stdpp Require Import numbers list strings.\nRequire Import Coq.Strings.Ascii.\nOpen Scope type_scope.\n'

  for (const [moduleIndex, module] of sortedModules.entries()) {
    const { environment, procedures, moduleName } = module
    const arrayIndex = 'arrayIndex' + moduleIndex

    const environmentCode = (() => {
      if (environment === null || environment.arrays.size === 0) {
        return `Definition environment${moduleIndex} : Environment False := {| arrayType := fun _ => False; arrays := fun _ => [] |}.
`
      }
      const arrayTypeFunction =
        'fun name => match name with ' +
        [...environment.arrays.entries()]
          .map(([name, { itemTypes }]) => {
            const coqType =
              itemTypes.length === 0
                ? 'unit'
                : itemTypes
                    .map((x) => (x === 'bool' ? 'bool' : 'Z'))
                    .join(' * ')
            return '| ' + sanitizeArray(moduleName, name) + ' => ' + coqType
          })
          .join(' ') +
        ' end'
      const arrayFunction =
        'fun name => match name with ' +
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
              return (
                '| ' +
                sanitizeArray(moduleName, name) +
                ' => ' +
                `repeat ${value} ${rawLength}`
              )
            }
          )
          .join(' ') +
        ' end'
      return (
        generateInductive(
          arrayIndex,
          [...environment.arrays.entries()].map(([x]) =>
            sanitizeArray(moduleName, x)
          )
        ) +
        '\n' +
        `Definition environment${moduleIndex} : Environment arrayIndex${moduleIndex} := {| arrayType := ${arrayTypeFunction}; arrays := ${arrayFunction} |}.

#[export] Instance arrayIndexEqualityDecidable${moduleIndex} : EqDecision arrayIndex${moduleIndex} := ltac:(solve_decision).
`
      )
    })()

    const decidableEquality = `#[export] Instance arrayTypeEqualityDecidable${moduleIndex} name : EqDecision (arrayType _ environment${moduleIndex} name).
Proof. simpl. repeat destruct name. all: solve_decision. Defined.
`

    const generatedCodeForProcedures = procedures
      .map(({ body, name: functionName, variables }) => {
        const variableIndex = sanitizeVariableIndex(moduleName, functionName)
        const header =
          generateInductive(
            variableIndex,
            [...variables.keys()].map((x) =>
              sanitizeVariable(moduleName, functionName, x)
            )
          ) +
          `#[export] Instance variableIndexEqualityDecidable${variableIndex} : EqDecision ${variableIndex} := ltac:(solve_decision).
` +
          'Definition ' +
          sanitizeFunction(moduleName, functionName) +
          ` (bools : ${variableIndex} -> bool) (numbers : ${variableIndex} -> Z) (addresses : ${variableIndex} -> list Z): Action (WithArrays _ (arrayType _ environment${moduleIndex})) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses `

        // every element of body is an Action returning absolutely anything
        const statements = body.map((statement) => {
          type BinderInfo = { number: number; type: 'int8' | 'int64' }
          const localBinderMap = new Map<string, BinderInfo>()
          let binderCounter = 0
          const liftExpression = (x: {
            expression: string
            type:
              | PrimitiveType
              | 'statement'
              | 'loop control'
              | 'condition'
              | PrimitiveType[]
          }): string => {
            if (binderCounter === 0) return x.expression
            if (x.type === 'loop control' || x.type === 'condition')
              return x.expression
            return `(liftToWithinLoop ${x.expression})`
          }
          let nestLevel = 0
          const dfs = (
            value: ValueType
          ): {
            expression: string
            type:
              | PrimitiveType
              | 'statement'
              | 'loop control'
              | 'condition'
              | PrimitiveType[]
          } => {
            const getBitWidth = (
              type: 'int8' | 'int16' | 'int32' | 'int64' | 'int256'
            ): 8 | 16 | 32 | 64 | 256 => {
              switch (type) {
                case 'int8':
                  return 8
                case 'int16':
                  return 16
                case 'int32':
                  return 32
                case 'int64':
                  return 64
                case 'int256':
                  return 256
              }
            }

            const getTuple = (value: ValueType[]) => {
              let tuple =
                'Done _ _ _ (' +
                value.map((_, i) => 'tuple_element_' + i).join(', ') +
                ')'
              for (const [index, element] of value.entries()) {
                tuple = `(${
                  dfs(element).expression
                } >>= fun tuple_element_${index} => ${tuple})`
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
                          return 'addInt ' + bitWidth
                        case 'subtract':
                          return 'subInt ' + bitWidth
                        case 'multiply':
                          return 'multInt ' + bitWidth
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
                      expression: `(${leftExpression} >>= fun x => ${rightExpression} >>= fun y => Done _ _ _ (bool_decide (x = y)))`,
                      type: 'bool',
                    }
                  case 'noteq':
                    return {
                      expression: `(${leftExpression} >>= fun x => ${rightExpression} >>= fun y => Done _ _ _ (bool_decide (x <> y)))`,
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
              case 'coerceInt64':
              case 'coerceInt256': {
                const integralType = (() => {
                  switch (value.type) {
                    case 'coerceInt8':
                      return 'int8'
                    case 'coerceInt16':
                      return 'int16'
                    case 'coerceInt32':
                      return 'int32'
                    case 'coerceInt64':
                      return 'int64'
                    case 'coerceInt256':
                      return 'int256'
                  }
                })()
                const bitWidth = (() => {
                  switch (value.type) {
                    case 'coerceInt8':
                      return 8
                    case 'coerceInt16':
                      return 16
                    case 'coerceInt32':
                      return 32
                    case 'coerceInt64':
                      return 64
                    case 'coerceInt256':
                      return 256
                  }
                })()
                const { type, expression } = dfs(value.value)
                assert(isNumeric(type) || type === 'bool')
                if (type === 'bool') {
                  return {
                    expression: `(coerceBool ${expression})`,
                    type: integralType,
                  }
                }
                return {
                  expression: `(${expression} >>= fun x => Done _ _ _ (coerceInt ${bitWidth} x))`,
                  type: integralType,
                }
              }
              case 'continue': {
                return {
                  expression: `(continue ${arrayIndex} (arrayType _ environment${moduleIndex}) ${variableIndex})`,
                  type: 'loop control',
                }
              }
              case 'break': {
                return {
                  expression: `(break ${arrayIndex} (arrayType _ environment${moduleIndex}) ${variableIndex})`,
                  type: 'loop control',
                }
              }
              case 'flush': {
                return {
                  expression: `(flush ${arrayIndex} (arrayType _ environment${moduleIndex}) ${variableIndex})`,
                  type: 'statement',
                }
              }
              case 'readChar': {
                return {
                  expression: `(readChar ${arrayIndex} (arrayType _ environment${moduleIndex}) ${variableIndex})`,
                  type: 'int8',
                }
              }
              case 'writeChar': {
                const { expression } = dfs(value.value)
                return {
                  expression: `(${expression} >>= fun x => writeChar ${arrayIndex} (arrayType _ environment${moduleIndex}) ${variableIndex} x)`,
                  type: 'statement',
                }
              }
              case 'get': {
                const variable = variables.get(value.name)
                assert(variable !== undefined)
                if (isNumeric(variable.type)) {
                  return {
                    expression: `(numberLocalGet ${arrayIndex} (arrayType _ environment${moduleIndex}) ${variableIndex} (${sanitizeVariable(
                      moduleName,
                      functionName,
                      value.name
                    )}))`,
                    type: variable.type,
                  }
                } else if (variable.type === 'bool') {
                  return {
                    expression: `(booleanLocalGet ${arrayIndex} (arrayType _ environment${moduleIndex}) ${variableIndex} (${sanitizeVariable(
                      moduleName,
                      functionName,
                      value.name
                    )}))`,
                    type: variable.type,
                  }
                } else if (variable.type === 'address') {
                  return {
                    expression: `(addressLocalGet ${arrayIndex} (arrayType _ environment${moduleIndex}) ${variableIndex} (${sanitizeVariable(
                      moduleName,
                      functionName,
                      value.name
                    )}))`,
                    type: variable.type,
                  }
                }
                assert(false)
              }
              case 'set': {
                const variable = variables.get(value.name)
                assert(variable !== undefined)
                const { expression } = dfs(value.value)
                if (isNumeric(variable.type)) {
                  return {
                    expression: `(${expression} >>= fun x => numberLocalSet ${arrayIndex} (arrayType _ environment${moduleIndex}) ${variableIndex} (${sanitizeVariable(
                      moduleName,
                      functionName,
                      value.name
                    )}) x)`,
                    type: 'statement',
                  }
                } else if (variable.type === 'bool') {
                  return {
                    expression: `(booleanLocalSet ${arrayIndex} (arrayType _ environment${moduleIndex}) ${variableIndex} (${sanitizeVariable(
                      moduleName,
                      functionName,
                      value.name
                    )}) ${expression})`,
                    type: 'statement',
                  }
                } else if (variable.type === 'address') {
                  return {
                    expression: `(addressLocalSet ${arrayIndex} (arrayType _ environment${moduleIndex}) ${variableIndex} (${sanitizeVariable(
                      moduleName,
                      functionName,
                      value.name
                    )}) ${expression})`,
                    type: 'statement',
                  }
                }
                assert(false)
              }
              case 'retrieve': {
                if (value.name === COMMUNICATION) {
                  const { expression: indexExpression } = dfs(value.index)
                  return {
                    expression: `(${indexExpression} >>= fun x => readByte ${arrayIndex} (arrayType _ environment${moduleIndex}) ${variableIndex} x)`,
                    type: 'int8',
                  }
                }
                assert(environment !== null)
                const declaration = environment.arrays.get(value.name)
                assert(declaration !== undefined)
                const { expression: indexExpression } = dfs(value.index)
                return {
                  expression: `(${indexExpression} >>= fun x => retrieve ${arrayIndex} (arrayType _ environment${moduleIndex}) ${variableIndex} (${sanitizeArray(
                    moduleName,
                    value.name
                  )}) x)`,
                  type: declaration.itemTypes,
                }
              }
              case 'store': {
                if (value.name === COMMUNICATION) {
                  const { expression: indexExpression } = dfs(value.index)
                  const { expression: valueExpression } = dfs(value.value)
                  return {
                    expression: `(${indexExpression} >>= fun x => ${valueExpression} >>= fun y => setByte ${arrayIndex} (arrayType _ environment${moduleIndex}) ${variableIndex} x y)`,
                    type: 'statement',
                  }
                }
                const { expression: indexExpression } = dfs(value.index)
                let tuple = getTuple(value.tuple)
                return {
                  expression: `(${indexExpression} >>= fun x => ${tuple} >>= fun y => store ${arrayIndex} (arrayType _ environment${moduleIndex}) ${variableIndex} (${sanitizeArray(
                    moduleName,
                    value.name
                  )}) x y)`,
                  type: 'statement',
                }
              }
              case 'less': {
                const { expression: leftExpression } = dfs(value.left)
                const { expression: rightExpression } = dfs(value.right)
                return {
                  expression: `(${leftExpression} >>= fun a => ${rightExpression} >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))`,
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
                  expression: `(${leftExpression} >>= fun a => ${rightExpression} >>= fun b => Done _ _ _ (bool_decide (Z.lt (${toSigned} a) (${toSigned} b))))`,
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
                      expression: `(${expression} >>= fun x => Done _ _ _ (negb x))`,
                      type,
                    }
                  }
                  case 'plus': {
                    return { expression, type }
                  }
                  case 'minus': {
                    return {
                      expression: `(${expression} >>= fun x => Done _ _ _ (-x))`,
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
                if (type === 'address') {
                  const { expression: indexExpression } = dfs(value.index)
                  return {
                    expression: `(${expression} >>= fun address => ${indexExpression} >>= fun index => nthTrap address index)`,
                    type: 'int8',
                  }
                }
                assert(Array.isArray(type))
                const length = type.length
                assert(value.index.type === 'literal')
                const index = Number(value.index.raw)
                // because of validation, this is nonnegative and less than length
                if (type.length === 1) return { expression, type: type[0] }
                const reverseIndex = length - index - 1
                let finalExpression = 'element_tuple'
                for (let i = 0; i < reverseIndex; i++)
                  finalExpression = 'fst (' + finalExpression + ')'
                finalExpression = `(snd (${finalExpression}))`
                return {
                  expression: `(${expression} >>= (fun element_tuple => Done _ _ _ ${finalExpression})`,
                  type: type[index],
                }
              }
              case 'call': {
                const { presetVariables, procedure } = value
                let numberMap = '(Done _ _ _ (fun x => 0%Z))'
                let booleanMap = '(Done _ _ _ (fun x => false))'
                for (const [name, value] of presetVariables.entries()) {
                  const { expression, type } = dfs(value)
                  assert(isNumeric(type) || type === 'bool')
                  if (isNumeric(type)) {
                    numberMap = `(${numberMap} >>= fun x => ${expression} >>= fun y => Done _ _ _ (update x (${sanitizeVariable(
                      moduleName,
                      procedure,
                      name
                    )}) y))`
                  } else {
                    booleanMap = `(${booleanMap} >>= fun x => ${expression} >>= fun y => Done _ _ _ (update x (${sanitizeVariable(
                      moduleName,
                      procedure,
                      name
                    )}) y))`
                  }
                }
                return {
                  expression: `(${numberMap} >>= fun x => ${booleanMap} >>= fun y => liftToWithLocalVariables (${sanitizeFunction(
                    moduleName,
                    procedure
                  )} y x))`,
                  type: 'statement',
                }
              }
              case 'condition': {
                const { condition, body, alternate } = value
                const processedCondition = dfs(condition)
                nestLevel++
                const bodyExpression = joinStatements(
                  body.map(dfs).map((x) => liftExpression(x)),
                  nestLevel
                )
                const alternateExpression = joinStatements(
                  alternate.map(dfs).map((x) => liftExpression(x)),
                  nestLevel
                )
                nestLevel--
                return {
                  expression: `(${liftExpression(
                    processedCondition
                  )} >>= fun x => if x then ${bodyExpression} else ${alternateExpression})`,
                  type: 'condition',
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

                nestLevel++
                const bodyExpression = joinStatements(
                  loopBody.map(dfs).map((x) => liftExpression(x)),
                  nestLevel
                )
                nestLevel--

                if (previousBinderValue === undefined)
                  localBinderMap.delete(functionName)
                else localBinderMap.set(loopVariable, previousBinderValue)
                binderCounter--

                if (end.type === 'literal' && end.valueType === 'string') {
                  return {
                    expression: `(loopString (${getCoqString(
                      end.raw
                    )}) (fun binder_${binderCounter}_intermediate => let binder_${binderCounter} := Done (WithLocalVariables ${arrayIndex} (arrayType _ environment${moduleIndex}) ${variableIndex}) withLocalVariablesReturnValue _ binder_${binderCounter}_intermediate in dropWithinLoop (${bodyExpression})))`,
                    type: 'statement',
                  }
                } else {
                  return {
                    expression: `(${
                      dfs(end).expression
                    } >>= fun x => loop (Z.to_nat x) (fun binder_${binderCounter}_intermediate => let binder_${binderCounter} := Done (WithLocalVariables ${arrayIndex} (arrayType _ environment${moduleIndex}) ${variableIndex}) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_${binderCounter}_intermediate)) 1%Z) in dropWithinLoop (${bodyExpression})))`,
                    type: 'statement',
                  }
                }
              }
              case 'cross module call': {
                const {
                  arrayMapping,
                  module: foreignModule,
                  presetVariables,
                  procedure,
                } = value
                let numberMap = '(Done _ _ _ (fun x => 0%Z))'
                let booleanMap = '(Done _ _ _ (fun x => false))'
                for (const [name, value] of presetVariables.entries()) {
                  const { expression, type } = dfs(value)
                  assert(isNumeric(type) || type === 'bool')
                  if (isNumeric(type)) {
                    numberMap = `(${numberMap} >>= fun x => ${expression} >>= fun y => Done _ _ _ (update x (${sanitizeVariable(
                      foreignModule,
                      procedure,
                      name
                    )}) y))`
                  } else {
                    booleanMap = `(${booleanMap} >>= fun x => ${expression} >>= fun y => Done _ _ _ (update x (${sanitizeVariable(
                      foreignModule,
                      procedure,
                      name
                    )}) y))`
                  }
                }
                const { arrayMappingText, congruence } = (() => {
                  if (environment === null || environment.arrays.size === 0)
                    return {
                      arrayMappingText: '(fun name => match name with end)',
                      congruence: 'ltac:(fun name => match name with end)',
                    }
                  const arrayMappingText =
                    '(fun name => match name with' +
                    [...arrayMapping.entries()]
                      .map(
                        ([inForeign, inCurrent]) =>
                          `| ${sanitizeArray(
                            foreignModule,
                            inForeign
                          )} => ${sanitizeArray(moduleName, inCurrent)}`
                      )
                      .join(' ') +
                    ' end)'
                  const congruence =
                    '(fun name => ltac:(destruct name; reflexivity))'
                  return { arrayMappingText, congruence }
                })()
                return {
                  expression: `(${numberMap} >>= fun x => ${booleanMap} >>= fun y => liftToWithLocalVariables (translateArrays (${sanitizeFunction(
                    foreignModule,
                    procedure
                  )} y x) (arrayType _ environment${moduleIndex}) ${arrayMappingText} ${congruence}))`,
                  type: 'statement',
                }
              }
              case 'communication area size': {
                return {
                  expression: `(getCommunicationSize _ _ _)`,
                  type: 'int64',
                }
              }
              case 'get money': {
                return { expression: '(getMoney _ _ _)', type: 'int256' }
              }
              case 'get sender': {
                return { expression: `(getSender _ _ _)`, type: 'address' }
              }
              case 'donate': {
                const { address, money } = value
                const { expression: addressExpression } = dfs(address)
                const { expression: moneyExpression } = dfs(money)
                return {
                  expression: `(${addressExpression} >>= fun address => ${moneyExpression} >>= fun money => donate _ _ _ money address)`,
                  type: 'statement',
                }
              }
              case 'construct address': {
                return {
                  expression:
                    '(' +
                    value.bytes
                      .map(
                        (x, index) =>
                          `${dfs(x).expression} >>= fun byte${index} => `
                      )
                      .join('') +
                    'Done _ _ _ [' +
                    value.bytes.map((_, index) => 'byte' + index).join(';') +
                    '])',
                  type: 'address',
                }
              }
              case 'invoke': {
                const { address, money, array, communicationSize } = value
                const { expression: addressExpression } = dfs(address)
                const { expression: moneyExpression } = dfs(money)
                const { expression: communicationSizeExpression } =
                  dfs(communicationSize)
                return {
                  expression: `(${addressExpression} >>= fun address => ${moneyExpression} >>= fun money => ${communicationSizeExpression} >>= fun size => @invokeWithArrays _ (arrayType _ environment${moduleIndex}) _ money address ${sanitizeArray(
                    moduleName,
                    array
                  )} size ltac:(reflexivity))`,
                  type: 'statement',
                }
              }
            }
          }
          return dfs(statement).expression
        })

        return header + joinStatements(statements, 0) + '.\n'

        function joinStatements(statements: string[], nestLevel: number) {
          statements.push('Done _ _ _ tt')
          return (
            '(' +
            (nestLevel ? '\n' + indent.repeat(nestLevel) : '') +
            statements.reduce(
              (accumulated, current) =>
                accumulated +
                ' >>=\n' +
                indent.repeat(nestLevel) +
                'fun _ => ' +
                current
            ) +
            (nestLevel ? '\n' : '') +
            indent.repeat(Math.max(nestLevel - 1, 0)) +
            ')'
          )
        }
      })
      .join('')

    code += environmentCode + decidableEquality + generatedCodeForProcedures
  }
  return code
}
