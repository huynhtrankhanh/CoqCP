import acorn from 'acorn'
import fs from 'fs'
import path from 'path'
import chokidar from 'chokidar'
import chalk from 'chalk'
import { Command } from 'commander'
import { CoqCPAST, CoqCPASTTransformer, ParseError } from './parse'
import { validateAST, ValidationError } from './validateAST'
import { sortModules } from './dependencyGraph'
import { coqCodegen } from './coqCodegen'
import { cppCodegen } from './cppCodegen'

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
  moduleNameToPath: Map<string, string>
): string[] {
  const errors: string[] = []
  const validationErrors = validateAST(modules)

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

// Utility function to generate output files
function generateOutput(
  sortedModules: CoqCPAST[],
  coqOutput: string,
  cppOutput: string
) {
  const coqCode = coqCodegen(sortedModules)
  fs.writeFileSync(coqOutput, coqCode, 'utf-8')

  const cppCode = cppCodegen(sortedModules)
  fs.writeFileSync(cppOutput, cppCode, 'utf-8')
}

// Compile function
function compile(files: string[], coqOutput: string, cppOutput: string) {
  const { modules, errors: parseErrors } = parseFiles(files)

  if (parseErrors.length > 0) {
    parseErrors.forEach((error) => console.error(error))
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
    moduleNameToPath
  )

  if (validationErrors.length > 0) {
    validationErrors.forEach((error) => console.error(error))
    return
  }

  generateOutput(sortedModules, coqOutput, cppOutput)
  console.log(chalk.green('Compilation successful!'))
}

// Watch and compile function
function watchAndCompile(
  files: string[],
  coqOutput: string,
  cppOutput: string
) {
  compile(files, coqOutput, cppOutput)
  chokidar.watch(files).on('change', () => {
    console.log(chalk.blue('File change detected. Recompiling...'))
    compile(files, coqOutput, cppOutput)
  })
}

// Main function
function main() {
  const program = new Command()

  program
    .name('coqcp-compiler')
    .version('1.0.0')
    .description(
      'CLI tool for compiling CoqCP source code files to Coq and C++ files'
    )
    .arguments('<coqOutput> <cppOutput> <inputFiles...>')
    .option('-w, --watch', 'Enable watch mode')
    .action((coqOutput, cppOutput, inputFiles, options) => {
      if (options.watch) {
        watchAndCompile(inputFiles, coqOutput, cppOutput)
      } else {
        compile(inputFiles, coqOutput, cppOutput)
      }
    })

  program.parse(process.argv)

  if (program.args.length < 3) {
    program.help()
  }
}

main()
