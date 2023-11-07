import { transformer } from './exampleCode'
import { coqCodegen } from './coqCodegen'
describe('coqCodegen function', () => {
  it('should produce correct Coq code', () => {
    const ast = transformer.transform()
    console.log(coqCodegen(ast))
    expect(false).toBe(true)
  })
})
