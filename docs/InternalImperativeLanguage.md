# Internal imperative language

The CoqCP project now includes a compiler. The compiler compiles an internal imperative language to both Coq and C++.

To work on the compiler, you will need to have Node.js installed. After that, switch to the `compiler` directory, and run `npm` to install the dependencies.

Then, you will need to run the `tsc` compiler in watch mode. To do this, run `npx tsc -w -p .`. The `tsc` compiler now monitors all changes to the TypeScript files and produces the corresponding files in the `dist` subdirectory.

The internal imperative language steals JavaScript syntax and interprets the parsed AST differently. As JavaScript syntax is stolen, the internal language is subject to every single JavaScript syntactic rule, including automatic semicolon insertion.

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

## Set a local variable

```js
set('variable_name' /* value */)
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

Numbers aren't intrinsically signed or unsigned in the language, instead this is determined by the operation you're using. For `+`, `-`, `*`, `|`, `^`, `&` and `~`, signedness doesn't really matter.

Overflow doesn't exist in this language. This language uses wraparound arithmetic.

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
set("array_name", /* array index */, [tupleElement1, tupleElement2, /* ... */])
```

Array index must be an int64.
