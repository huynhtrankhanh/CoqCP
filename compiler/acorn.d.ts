import { Options } from 'acorn'
import * as ESTree from 'estree'

declare module 'acorn' {
  type ExtendNode<T> = {
    [K in keyof T]: T[K] extends object | null | undefined
      ? ExtendNode<T[K]>
      : T[K]
  } & (T extends ESTree.Node
    ? {
        start: number
        end: number
        loc: {
          start: { line: number; column: number }
          end: { line: number; column: number }
        }
      }
    : T)

  export function parse(s: string, o: Options): ExtendNode<ESTree.Program>
}
