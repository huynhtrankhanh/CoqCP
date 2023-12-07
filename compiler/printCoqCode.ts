import { transformer } from './exampleCode'
import { coqCodegen } from './coqCodegen'

process.stdout.write(coqCodegen(transformer.transform()))