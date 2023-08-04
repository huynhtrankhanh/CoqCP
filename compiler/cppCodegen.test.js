import { CoqCPASTTransformer } from './parse'
import { cppCodegen } from './cppCodegen' // replace with actual path to module

const code = `...` // Your existing code
const transformer = new CoqCPASTTransformer(code)

describe('cppCodegen function', () => {
  it('should produce correct C++ include statement', () => {
    const ast = transformer.transform()
    const cppCode = cppCodegen(ast)
    expect(cppCode).toEqual('#include<bits/stdc++.h>')
  })
})
