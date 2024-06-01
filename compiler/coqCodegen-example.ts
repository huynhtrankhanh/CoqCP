import { coqCodegen } from "./coqCodegen"
import { sortModules } from "./dependencyGraph"
import { CoqCPASTTransformer } from "./parse"

const program1 = [
    `procedure("main", {}, () => {
        range("Hello", x => { writeChar(x); })
    })`
]

const program2 = [
    `module(wow);
    procedure("wow", {}, () => {
        range("Hello", x => { writeChar(x); })
    })`,
    `procedure("main", {}, () => {
        call(wow, {}, "wow", {});
    })`
]

const program3 = [
    `module(PrintDigit);
    environment({ digit: array([int8], 1) })
    procedure("printer", {}, () => {
        writeChar(retrieve("digit", 0)[0]);
    })`,
    `environment({ data: array([int8], 1) })
    procedure("main", {}, () => {
        call(PrintDigit, { digit: "data" }, "printer", {})
    })`
]

const generate = (modules: string[]) => {
    const sorted = sortModules(modules.map(x => {
        const transformer = new CoqCPASTTransformer(x)
        return transformer.transform()
    }))
    return coqCodegen(sorted)
}

process.stdout.write(generate(program3))