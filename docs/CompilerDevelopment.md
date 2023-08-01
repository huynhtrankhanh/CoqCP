# Compiler Development
The CoqCP project now includes a compiler. The compiler compiles a custom language to both Coq and C++.

To work on the compiler, you will need to have Node.js installed. After that, switch to the `compiler` directory, and run `npm` to install the dependencies.

Then, you will need to run the `tsc` compiler in watch mode. To do this, run `npx tsc -w -p .`. The `tsc` compiler now monitors all changes to the TypeScript files and produces the corresponding files in the `dist` subdirectory.
