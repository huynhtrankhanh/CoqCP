// Import necessary libraries/modules
import * as fs from 'fs'
import * as path from 'path'
import * as glob from 'glob'
import * as chokidar from 'chokidar'
import yargs from 'yargs/yargs'
import { hideBin } from 'yargs/helpers'

// Import necessary modules for transform function
import { CoqCPASTTransformer, CoqCPAST, ParseError } from './parse'
import { validateAST } from './validateAST'
import { coqCodegen } from './coqCodegen'
import { cppCodegen } from './cppCodegen'

// Define transform function
function transform(
  fileContent: string,
  cppOutputPath: string,
  coqOutputPath: string
) {
  let ast: CoqCPAST | undefined
  try {
    const transformer = new CoqCPASTTransformer(fileContent)
    ast = transformer.transform()
  } catch (error) {
    // Print error here
    if (!(error instanceof ParseError) && !(error instanceof SyntaxError))
      throw error
    console.error(`Error transforming file`, error)
  }
  if (ast === undefined) return

  const errors = validateAST(ast)

  // Print errors in a user-friendly format
  if (errors.length !== 0) {
    console.error('Validation Errors:')
    errors.forEach((error) => {
      switch (error.type) {
        case 'binary expression expects numeric':
        case 'instruction expects numeric':
        case 'binary expression expects boolean':
        case 'binary expression type mismatch':
        case 'instruction type mismatch':
          console.error(`${error.type} at ${JSON.stringify(error.location)}`)
          console.error(
            `Actual Types: ${error.actualType1}, ${error.actualType2}`
          )
          break
        case 'variable type mismatch':
          console.error(`${error.type} at ${JSON.stringify(error.location)}`)
          console.error(`Actual Type: ${error.actualType}`)
          break
        case 'expression no statement':
        case 'procedure not found':
        case 'variable not present':
        case 'condition must be boolean':
        case 'no surrounding range command':
        case 'undefined variable':
        case 'undefined binder':
        case 'not representable int64':
        case 'bad number literal':
        case 'range end must be int64':
        case 'instruction expects int8':
        case 'instruction expects int64':
        case 'instruction expects tuple':
        case 'undefined array':
        case 'index out of bounds':
        case 'unary operator expects numeric':
        case "unary operator can't operate on tuples":
        case 'unary operator expects boolean':
        case "array length can't be negative":
          console.error(`${error.type} at ${JSON.stringify(error.location)}`)
          break
      }
    })
    return
  }

  const coqCode = coqCodegen(ast)
  fs.writeFileSync(coqOutputPath, coqCode)

  const cppCode = cppCodegen(ast)
  fs.writeFileSync(cppOutputPath, cppCode)

  console.log(
    `Transformation completed for ${cppOutputPath} and ${coqOutputPath}`
  )
}

const argv = yargs(hideBin(process.argv))
  .option('input', {
    alias: 'i',
    description: 'Input files glob pattern',
    demandOption: true,
    type: 'string',
  })
  .option('coqOutput', {
    alias: 'co',
    description: 'Coq output directory',
    demandOption: true,
    type: 'string',
  })
  .option('cppOutput', {
    alias: 'cp',
    description: 'C++ output directory',
    demandOption: true,
    type: 'string',
  })
  .option('watch', {
    alias: 'w',
    description: 'Watch mode',
    type: 'boolean',
  })
  .parseSync()

// Function to process files based on the provided glob pattern
function processFiles(globPattern: string) {
  glob
    .glob(globPattern)
    .then((files) => files.forEach((file) => transformFile(file)))
}

// Define the transform function for a file
function transformFile(filePath: string) {
  const fileContent = fs.readFileSync(filePath, 'utf8')
  const fileName = path.basename(filePath, path.extname(filePath))

  // Assuming coq and cpp output files have the same name
  const coqOutputPath = path.join(argv.coqOutput, `${fileName}.v`)
  const cppOutputPath = path.join(argv.cppOutput, `${fileName}.cpp`)

  transform(fileContent, cppOutputPath, coqOutputPath)
}

// Initial processing of files
processFiles(argv.input)

// Watch mode using chokidar
if (argv.watch) {
  const watcher = chokidar.watch(argv.input, { ignoreInitial: true })

  watcher.on('all', (event, filePath: string) => {
    console.log(`${filePath} ${event}`)
    transformFile(filePath)
  })
}
