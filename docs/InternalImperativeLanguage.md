# Internal imperative language

The CoqCP project now includes a compiler. The compiler compiles an internal imperative language to both Coq and C++.

To work on the compiler, you will need to have Node.js installed. After that, switch to the `compiler` directory, and run `npm` to install the dependencies.

Then, you will need to run the `tsc` compiler in watch mode. To do this, run `npx tsc -w -p .`. The `tsc` compiler now monitors all changes to the TypeScript files and produces the corresponding files in the `dist` subdirectory.

The internal imperative language steals JavaScript syntax and interprets the parsed AST differently. As JavaScript syntax is stolen, the internal language is subject to every single JavaScript syntactic rule, including automatic semicolon insertion.

The documentation for this language isn't very precise. I hope you can fill in the gaps by reading the generated Coq and C++ code.

A source file consists of 0 or 1 `environment` block and any number of `procedure` blocks.

The `environment` block can be placed at the top, at the bottom or between procedures.

Here is an example of an `environment` block.

```js
environment({
  fibSeq: array([int32], 100),
  anotherArray: array([int8, int64], 3),
})
```

In the above example, we declare two arrays `fibSeq` and `anotherArray`. `fibSeq` is an array of 100 elements, each element has a type of `[int32]`. `anotherArray` is an array of 3 elements, each element has a type of `[int8, int64]`.

The permitted primitive types are `int8`, `int16`, `int32`, `int64` and `bool`.

Here is an example of a procedure.

```js
procedure('hello', { var1: int8 }, () => {
  // ...
})
```

The first argument is the procedure name. The second argument is an object literal representing local variables for the procedure. The key represents the variable name, and the value represents the primitive type.

Within a procedure, there are several commands.

## Number literal

```js
0
```

```js
1
```

```go
-1
```

```js
998244353
```

Only integers are allowed. Number literals are always interpreted as `int64`.

**In general, numbers are treated as unsigned unless you use a command specifically for signed numbers.** If you write a negative number, it will be silently converted to its unsigned equivalent.

## String literal

```js
'hello'
```

```js
'đi chơi không'
```

```js
'自我解放吧！'
```

String literals can only be used with `range()`.

## Set a local variable

```js
set('variable_name', value)
```

This is a statement and doesn't return.

## Get a local variable

```js
get('variable_name')
```

The return type depends on the variable type.

## Arithmetic

These operators are supported: `+`, `-`, `*`, `|`, `^`, `&`, `~`.

To divide, you can use `divide(x, y)` (unsigned) or `sDivide(x, y)` (signed).

**In general, numbers are treated as unsigned unless you use a command specifically for signed numbers.**

Only the `sDivide` command has overflow. All other commands use wraparound arithmetic.

## Read character

```js
readChar()
```

Returns an `int64`. Return value fits within `int8` range if end of file is not reached. If end of line is reached, `readChar()` returns `int64` `-1`.

## Write character

```js
writeChar(x)
```

Takes a single `int8` as argument.

## Boolean Operators

These operators are allowed: `||`, `&&` and `!`.

## Comparison

`==` and `!=` can be used on both numbers and booleans, provided that the values on both sides are of the same type.

You can use `less(x, y)` (unsigned) and `sLess(x, y)` (signed) to check whether x is less than y. Both x and y must be numbers and of the same type.

## Coercion

You can coerce any boolean or number to a numeric type.

**Booleans:** If you coerce `false`, you get `0`. If you coerce `true`, you get `1`.

The coercion commands are `coerceInt8`, `coerceInt16`, `coerceInt32` and `coerceInt64`.

## Get global array element

```js
retrieve("array_name", /* array index */)[/* tuple index */]
```

Tuple index must be a literal number. Array index must be an `int64`.

## Set global array element

```js
store("array_name", /* array index */, [tupleElement1, tupleElement2, /* ... */])
```

Array index must be an `int64`.

## `if`/`else`

```js
if (condition) {
  // ...
} else {
  // ...
}
```

Same syntax as JavaScript. `{}` (curly brackets) are mandatory.

`else if` isn't supported.

## Loop

### Numeric

```js
range(endValue, (counter) => {
  // ...
})
```

`endValue` is an `int64`. The `counter` is also an `int64`. The counter goes from 0 to endValue - 1, similar to `for i in range(x)` in Python.

Within a `range` command, you can use `"break"` (**not `break`**) and `"continue"` (**not `continue`**).

Example:

```js
range(endValue, (counter) => {
  if (less(counter, 5)) {
    ;('break')
  }
  ;('continue')
})
```

### String literal

```js
range('Hello, World!', (x) => {
  writeChar(x)
})
```

Iterates over all bytes of the UTF-8 representation of the string. `x` is of type `int8`. Each byte might or might not represent a character.

## Procedure call

### Within the same module

```js
call('procedure_name', {
  a: 5,
  b: 6,
})
```

When calling a procedure, you can preset some of its local variables. The remaining local variables are initialized to 0 if the variable is numeric and false if the variable is boolean. A procedure call is a statement and doesn't have a return value.

It is only possible to call functions that are already declared. Recursion is not allowed.

### Cross module calls

```js
call(
  moduleName,
  {
    array1: 'arrayA',
    array2: 'arrayB',
  },
  'procedure name',
  { a: 5, b: 6 }
)
```

The first two parameters are the module name and the array mapping, respectively. The module name isn't a string, it is written without quotes. The two remaining variables are the procedure name and the preset variables.

**Array mapping:** When calling a procedure in another module, you have to supply the module with all the arrays it declares in its `environment` block. This creates a mapping between the arrays in the external module and the arrays in the current module. When calling a procedure in another module, that external module can't create arrays on its own.
