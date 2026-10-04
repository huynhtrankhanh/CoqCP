import { ValueType } from './parse'

const isPure = (value: ValueType): boolean => {
  switch (value.type) {
    case 'binaryOp':
      return isPure(value.left) && isPure(value.right)
    case 'break':
      return false
    case 'call':
      return false
    case 'coerceInt16':
    case 'coerceInt32':
    case 'coerceInt64':
    case 'coerceInt8':
      return isPure(value.value)
    case 'condition':
      return false
    case 'continue':
      return false
    case 'divide':
      return isPure(value.left) && isPure(value.right)
    case 'flush':
      return false
    case 'get':
      return true
    case 'set':
      return false
    case 'less':
      return isPure(value.left) && isPure(value.right)
    case 'literal':
      return true
    case 'local binder':
      return true
    case 'range':
      return false
    case 'readChar':
      return false
    case 'retrieve':
      return true
    case 'sDivide':
      return isPure(value.left) && isPure(value.right)
    case 'sLess':
      return isPure(value.left) && isPure(value.right)
    case 'store':
      return false
    case 'subscript':
      return isPure(value.value)
    case 'unaryOp':
      return isPure(value.value)
    case 'writeChar':
      return false
    case 'cross module call':
      return false
    case 'grow':
      return false
  }
}

export default isPure
