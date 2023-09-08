type ValidationError =
  | { type: 'UnaryOperatorTypeMismatch'; operator: UnaryOp; valueType: ValueType }
  | { type: 'BinaryOperatorTypeMismatch'; operator: BinaryOp; leftType: ValueType; rightType: ValueType }
  | { type: 'BinaryOperatorTypeMismatch'; operator: BinaryOp; leftType: ValueType; rightType: ValueType; location: Location }
  | { type: 'InvalidExpressionType'; expectedType: string; actualType: ValueType; location: Location }
  | { type: 'UnknownValueType'; valueType: ValueType }
  | { type: 'ConditionValueTypeMismatch'; conditionType: ValueType; location: Location }
  | { type: 'InvalidTypeForCoercion'; valueType: ValueType; targetPrimitiveType: PrimitiveType };

function validateAST(node: Instruction, environment: Environment): ValidationError[] {
  const errors: ValidationError[] = [];

  function validateBinaryOp(node: BinaryOperationInstruction) {
    const { operator, left, right } = node;

    if (operator === 'add' || operator === 'subtract' || operator === 'multiply' || operator === 'divide') {
      const leftType = validateExpressionType(left);
      const rightType = validateExpressionType(right);
      if (leftType !== rightType) {
        errors.push({ type: 'BinaryOperatorTypeMismatch', operator, leftType, rightType });
      }
    }

    // Handle other binary operators in a similar manner.
  }

  function validateUnaryOp(node: UnaryOperationInstruction) {
    const { operator, value } = node;

    if (operator === 'minus' || operator === 'plus') {
      const valueType = validateExpressionType(value);
      if (valueType !== 'int8' && valueType !== 'int16' && valueType !== 'int32' && valueType !== 'int64') {
        errors.push({ type: 'UnaryOperatorTypeMismatch', operator, valueType });
      }
    }

    // Handle other unary operators in a similar manner.
  }

  function validateExpressionType(expression: ValueType): string {
    if (expression.type === 'local binder') {
      const variable = environment.arrays.get(expression.name);
      if (variable) {
        return variable.type;
      }
    } else if (expression.type === 'literal') {
      return expression.valueType;
    } else if (expression.type === 'binaryOp') {
      validateBinaryOp(expression);
    } else if (expression.type === 'unaryOp') {
      validateUnaryOp(expression);
    }

    errors.push({ type: 'UnknownValueType', valueType: expression });
    return '';
  }

  validateExpressionType(node);

  return errors;
}

function emitErrorMessage(error: ValidationError): string {
  switch (error.type) {
    case 'UnaryOperatorTypeMismatch':
      return `Unary operator '${error.operator}' is applied to an incompatible type: ${error.valueType}`;
    case 'BinaryOperatorTypeMismatch':
      return `Binary operator '${error.operator}' is applied to incompatible types: ${error.leftType} and ${error.rightType}`;
    case 'InvalidExpressionType':
      return `Invalid expression type. Expected: ${error.expectedType}, Actual: ${error.actualType}`;
    case 'UnknownValueType':
      return `Unknown value type: ${error.valueType}`;
    case 'ConditionValueTypeMismatch':
      return `Condition value type mismatch. Expected: boolean, Actual: ${error.conditionType}`;
    case 'InvalidTypeForCoercion':
      return `Invalid type for coercion. Value type: ${error.valueType}, Target primitive type: ${error.targetPrimitiveType}`;
    default:
      return 'Unknown error';
  }
}

// Example usage:
const environment: Environment = {
  arrays: new Map(),
};

const astNode: Instruction = /* Your AST root node here */;

const validationErrors = validateAST(astNode, environment);

if (validationErrors.length > 0) {
  console.error("Validation Errors:");
  for (const error of validationErrors) {
    console.error(emitErrorMessage(error));
  }
} else {
  console.log("AST is valid.");
}
