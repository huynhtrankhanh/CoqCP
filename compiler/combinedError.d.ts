import { ValidationError } from './validateAST'
export type CombinedError =
  | { type: 'parse error'; message: string }
  | { type: 'validation error'; errors: ValidationError[] }
