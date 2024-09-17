import acorn from 'acorn'
import fs from 'fs'
import path from 'path'
import chokidar from 'chokidar'
import chalk from 'chalk'
import { Command } from 'commander'
import { CoqCPAST, CoqCPASTTransformer, ParseError } from './parse'
import { validateAST } from './validateAST'
import { sortModules } from './dependencyGraph'
import { coqCodegen } from './coqCodegen'
import { cppCodegen } from './cppCodegen'
import { solidityCodegen } from './solidityCodegen'
// Utility function to parse files
function parseFiles(files: string[]): {
  modules: CoqCPAST[]
  errors: string[]
} {
  const modules: CoqCPAST[] = []
  const errors: string[] = []

  files.forEach((file) => {
    try {
      const code = fs.readFileSync(file, 'utf-8')
      const transformer = new CoqCPASTTransformer(code)
      modules.push(transformer.transform())
    } catch (error) {
      if (error instanceof ParseError || error instanceof SyntaxError) {
        errors.push(chalk.red(`Error in file ${file}: ${error.message}`))
      } else {
        throw error
      }
    }
  })

  return { modules, errors }
}

// Utility function to validate modules
function validateModules(
  modules: CoqCPAST[],
  modulePathMap: Map<CoqCPAST, string>,
  moduleNameToPath: Map<string, string>,
  blockchain: boolean
): string[] {
  const errors: string[] = []
  const validationErrors = validateAST(modules, blockchain)

  validationErrors.forEach((error) => {
    const filePath =
      'module' in error
        ? modulePathMap.get(error.module)
        : moduleNameToPath.get(error.location.moduleName)
    errors.push(
      chalk.red(`Validation Error in file ${filePath}: ${error.type}`)
    )
    errors.push(chalk.yellow(`Details: ${JSON.stringify(error, null, 2)}`))
  })

  return errors
}

// Compile function
function compile(
  files: string[],
  coqOutput: string,
  cppOutput: string,
  blockchain: boolean
) {
  const { modules, errors: parseErrors } = parseFiles(files)

  if (parseErrors.length > 0) {
    parseErrors.forEach((error) => console.error(error))
    process.exit(1)
    return
  }

  const modulePathMap = new Map(
    modules.map((module, index) => [module, files[index]])
  )
  const moduleNameToPath = new Map(
    modules.map((module, index) => [module.moduleName, files[index]])
  )
  const sortedModules = sortModules(modules)
  const validationErrors = validateModules(
    sortedModules,
    modulePathMap,
    moduleNameToPath,
    blockchain
  )

  if (validationErrors.length > 0) {
    validationErrors.forEach((error) => console.error(error))
    process.exit(1)
    return
  }

  const coqCode = coqCodegen(sortedModules)
  fs.writeFileSync(coqOutput, coqCode, 'utf-8')

  if (blockchain) {
    const solidityCode = solidityCodegen(sortedModules)
    fs.writeFileSync(cppOutput, solidityCode, 'utf-8')
  } else {
    const cppCode = cppCodegen(sortedModules)
    fs.writeFileSync(cppOutput, cppCode, 'utf-8')
  }
  console.log(chalk.green('Compilation successful!'))
}

// Watch and compile function
function watchAndCompile(
  files: string[],
  coqOutput: string,
  cppOutput: string,
  blockchain: boolean
) {
  compile(files, coqOutput, cppOutput, blockchain)
  chokidar.watch(files).on('change', () => {
    console.log(chalk.blue('File change detected. Recompiling...'))
    compile(files, coqOutput, cppOutput, blockchain)
  })
}

// Main function
function main() {
  if (process.argv[3] === '?json') {
    const filename = process.argv[4]
    if (filename === undefined) {
      console.log('No file name specified')
      process.exit(1)
      return
    }
    const content = fs.readFileSync(filename, { encoding: 'utf8' })
    const { type } = content
    if (type === 'blockchain') {
      const { inputs, solidityOutput, coqOutput } = content
      if (!Array.isArray(inputs)) {
        console.log('inputs must be an array')
        process.exit(1)
        return
      }
      const newInputs: string = []
      for (const input of inputs) {
        if (typeof input !== 'string') {
          console.log(JSON.stringify(input) + " isn't a string")
          process.exit(1)
          return
        }
        newInputs.push(input)
      }
      if (typeof coqOutput !== 'string') {
        console.log('coqOutput must be a string')
        process.exit(1)
        return
      }
      if (typeof solidityOutput !== 'string') {
        console.log('solidityOutput must be a string')
        process.exit(1)
        return
      }
    } else if (type === 'competitive') {
      const { inputs, cppOutput, coqOutput } = content
      if (!Array.isArray(inputs)) {
        console.log('inputs must be an array')
        process.exit(1)
        return
      }
      const newInputs: string = []
      for (const input of inputs) {
        if (typeof input !== 'string') {
          console.log(JSON.stringify(input) + " isn't a string")
          process.exit(1)
          return
        }
        newInputs.push(input)
      }
      if (typeof coqOutput !== 'string') {
        console.log('coqOutput must be a string')
        process.exit(1)
        return
      }
      if (typeof cppOutput !== 'string') {
        console.log('cppOutput must be a string')
        process.exit(1)
        return
      }
    } else {
      console.log('Unrecognized type')
      process.exit(1)
      return
    }
    return
  }

  const program = new Command()

  program
    .name('coqcp-compiler')
    .version('1.0.0')
    .description(
      'CLI tool for compiling CoqCP source code files to Coq and C++ files'
    )
    .arguments('<coqOutput> <cppOutput> <inputFiles...>')
    .option('-w, --watch', 'Enable watch mode')
    .option('-b, --blockchain', 'Enable blockchain mode')
    .action((coqOutput, cppOutput, inputFiles, options) => {
      if (options.watch) {
        watchAndCompile(inputFiles, coqOutput, cppOutput, options.blockchain)
      } else {
        compile(inputFiles, coqOutput, cppOutput, options.blockchain)
      }
    })

  program.parse(process.argv)

  if (program.args.length < 3) {
    program.help()
  }
}

main()
