These programs are not written in JavaScript. They are not written in any dialect of JavaScript. They are written in a language that steals JavaScript syntax. See [the documentation](../docs/InternalImperativeLanguage.md).

All configurations use competitive mode and emit Coq and C++ (`.cpp`) files. Inputs are whitespace-separated unsigned integers; outputs are decimal integers followed by newlines. Compile an example with `node compiler/dist/cli '?json' programs/Knapsack.module.json`, then `g++ -std=c++20 generated-cpp/Knapsack.cpp -o /tmp/knapsack`.

| Example                     | Input                                            | Output                           |
| --------------------------- | ------------------------------------------------ | -------------------------------- |
| Knapsack                    | `n capacity`, then `n` pairs of weight and value | Maximum total value              |
| BuyLowSellHigh              | `n`, then `n` prices                             | Maximum trading profit           |
| DisjointSetUnion            | `q`, then `q` pairs of vertices in `0..99`       | Component size after each union  |
| MajorityElement             | `n`, then `n` values with a strict majority      | Majority value                   |
| llmGeneratedCode/BubbleSort | `n`, then `n` values                             | Sorted values, one per line      |
| llmGeneratedCode/MaxElement | `n`, then `n` values                             | Maximum, or zero for empty input |

The examples that need variable capacity use `grow()` before indexing beyond their initial array sizes.
