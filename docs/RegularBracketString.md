# Regular bracket strings
Regular bracket strings, also called Dyck words, are defined as follows:
- An empty string is a regular bracket string
- If you have a regular bracket string, you can put a `(` in front and `)` at the end of the string to make another regular bracket string
- If you have two regular bracket strings, you can concatenate them together to make another regular bracket string

In [`RegularBracketString.v`](../theories/RegularBracketString.v), this definition is named `isBalanced`.

There are many competitive programming problems about regular bracket strings. Every competitive programming problem about regular bracket strings is a novel snowflake.

Here are some results about these strings.

**There is another way to describe regular bracket strings**

There is another definition of regular bracket strings that is widely used in the competitive programming community: For a string to be a regular bracket string, the number of `(` characters must be equal to the number of `)` characters and for every prefix of the string, the number of `)` characters must not exceed the number of `(` characters. In [`RegularBracketString.v`](../theories/RegularBracketString.v), this definition is named `balanceFactorBasedDefinition`.

We now prove that this definition is equivalent to the inductive definition `isBalanced` above.

First, we prove `isBalanced` implies `balanceFactorBasedDefinition`.

Let `countOpen(s)` be the number of `(` characters in `s`, and `countClose(s)` be the number of `)` characters in `s`.

We perform induction on the `isBalanced` predicate. There are three cases to consider.

Case 1: Empty string. Since it is an empty string, the number of `(` is equal to the number of `)`. Furthermore, since it is an empty string, its only prefix is also an empty string. Both conditions of `balanceFactorBasedDefinition` are satisfied.

Case 2: The current string `s` is equal to `"(" + s' + ")"`, where `s'` is a string that satisfies `balanceFactorBasedDefinition`. We have `countOpen(s) = countOpen(s') + 1`, and `countClose(s) = countClose(s') + 1`. Since `countOpen(s') = countClose(s')`, we have `countOpen(s) = countClose(s)`. The string now satisfies the first condition of `balanceFactorBasedDefintion`.

To prove that the string `s` satisfies the second condition of `balanceFactorBasedDefinition`, we need to consider several cases.

- The prefix `s1` of `s` is empty. Since the prefix is empty, `countOpen(s1) = countClose(s1) = 0`, therefore `countOpen(s1) >= countClose(s1)`.
- The prefix `s1` is equal to `"(" + s2`, where `s2` is a prefix of `s'`. We have `countOpen(s1) = countOpen(s2) + 1`, and `countClose(s1) = countClose(s2)`. As `s2` is a prefix of `s'`, we have `countOpen(s2) >= countClose(s2)`. So `countOpen(s1) = countOpen(s2) + 1 >= countClose(s2) + 1 >= countClose(s1)`.
- The prefix `s1` is identical to `s`. Since this prefix is identical to `s`, `countOpen(s1) = countClose(s1)`, therefore `countOpen(s1) >= countClose(s1)`.

Now the string `s` satisfies both conditions.

Case 3: The current string `s` is the concatenation of two strings `s1` and `s2`. Both `s1` and `s2` satisfy the `balanceFactorBasedDefinition` conditions. Since `s1` satisfies `balanceFactorBasedDefinition`, `countOpen(s1) = countClose(s1)`. Additionally, since `s2` satisfies `balanceFactorBasedDefinition`, `countOpen(s2) = countClose(s2)`. Since the current string `s` is the concatenation of `s1` and `s2`, `countOpen(s) = countOpen(s1) + countOpen(s2)`. Therefore, `countClose(s) = countClose(s1) + countClose(s2) = countOpen(s1) + countOpen(s2) = countOpen(s)`, thus satisfying the first condition of `balanceFactorBasedDefinition`.

To prove that the string `s` satisfies the second condition of `balanceFactorBasedDefinition`, we need to consider two cases. If the prefix `s'` of `s` is also a prefix of `s1`, `countOpen(s') >= countClose(s')`. Otherwise, the prefix `s'` is equal to `s1 + s''`, where `s''` is a prefix of `s2`. Now, `countOpen(s1) = countClose(s1)`, and `countOpen(s'') >= countClose(s'')`, so `countOpen(s1) + countOpen(s'') >= countClose(s1) + countClose(s'')`, therefore `countOpen(s') >= countClose(s')`.

Now the string `s` satisfies both conditions.

We now prove `balanceFactorBasedDefinition` implies `isBalanced`.

We perform induction on the length of the string `s`.

We handle several special cases first.

First, if the string `s` is empty, it already satisfies `isBalanced`.

Second, if the string `s` consists of a single character, we have two cases.
- If `s = "("`, `countOpen(s) = 1` and `countClose(s) = 0`, therefore `countOpen(s)` is not equal to `countClose(s)`. Therefore the string does not satisfy `balanceFactorBasedDefinition`. We can ignore this case.
- If `s = "("`, `countOpen(s) = 0` and `countClose(s) = 1`, therefore `countOpen(s)` is not equal to `countClose(s)`. Therefore the string does not satisfy `balanceFactorBasedDefinition`. We can ignore this case.

Now we need to consider the case where the length of `s` is at least 2 and satisfies `balanceFactorBasedDefinition`.

We need to prove a small fact: `s` can always be decomposed as `"(" + s1 + ")"`. `s1` might not necessarily satisfy `balanceFactorBasedDefinition`.
- First character: We consider the case where the first character is `)`. We take a prefix of length 1 of the string. Since `countOpen(")") = 0`, and `countClose(")") = 1`, this means `countOpen(")") < countClose(")")`, which is a contradiction. The first character is always `(`.
- Last character: `s` is equal to `s' + a`, where `a` is a single character. We have `countOpen(s') >= countClose(s')`, and `countOpen(s' + a) = countClose(s' + a)`. We consider the case where `a` is `(`. We have `countOpen(s' + "(") = countOpen(s') + 1`. Also, we have `countClose(s' + "(") = countClose(s')`. Therefore `countOpen(s') + 1 = countClose(s')`, which means `countOpen(s') < countClose(s')`, which is a contradiction. The last character is always `)`.

We now consider two cases.
- For all prefixes `s'` of length from 1 to `length(s) - 1` (inclusive), `countOpen(s') > countClose(s')`. We decompose `s` as `"(" + s1 + ")"`. As `countOpen(s) = countClose(s)`, and `countOpen(s) = countOpen(s1) + 1`, `countClose(s) = countClose(s1) + 1`, we have `countOpen(s1) = countClose(s1)`. This means `s1` satisfies the first condition of `balanceFactorBasedDefinition`. For all prefixes `s'` of `s1`, we take a prefix `t` of length `length(s') + 1` of the string `s`. We have `countOpen(t) > countClose(t)` and as `t = "(" + s'`, we have `countOpen(s') + 1 > countClose(s')`. Therefore, `countOpen(s') >= countClose(s')`. Now the string `s1` satisfies the second condition of `balanceFactorBasedDefinition`. As `s1` satisfies `balanceFactorBasedDefinition`, and the length of `s1` is less than the length of `s`, we can apply the induction hypothesis to deduce that `s1` satisfies `isBalanced`. As `s1` satisfies `isBalanced`, `"(" + s1 + ")"` satisfies `isBalanced` and thus `s` satisfies `isBalanced`.
- There exists a prefix `s1` of length from `1` to `length(s) - 1` (inclusive) where `countOpen(s1) = countClose(s1)`. Every prefix of `s1` is also a prefix of `s`, so `s'` satisfies `balanceFactorBasedDefinition`. As the length of `s1` is less than the length of `s` and `s1` satisfies `balanceFactorBasedDefinition`, we can apply the induction hypothesis to deduce that `s1` satisfies `isBalanced`. The string `s` can be decomposed as `s1 + s2`. As `countOpen(s) = countClose(s)` and `countOpen(s1) + countClose(s1)`, we deduce that `countOpen(s2) = countClose(s2)`. For every prefix `s'` of `s2`, we take a prefix `t` of length `length(s1) + length(s')` from `s`. We have `countOpen(t) >= countClose(t)`. We have `t = s1 + s'`, and as `countOpen(s1) = countClose(s1)`, we have `countOpen(s2) >= countClose(s2)`. Now `s2` satisfies `balanceFactorBasedDefinition`. As `s2` satisfies `balanceFactorBasedDefinition` and the length of `s2` is less than the length of `s`, we can apply the induction hypothesis to deduce that `s2` satisfies `isBalanced`. As both `s1` and `s2` satisfy `isBalanced`, the concatenation also satisfies `isBalanced` and thus `s` satisfies `isBalanced`.

Therefore the two definitions are equivalent.

**Given a string with `(`, `)` and `?`, there is a quick way to check if it is possible to replace the question marks with `(` and `)` to make a regular bracket string**

Let the number of already filled `(` characters be `filledOpen`. Similarly, let the number of already filled `)` characters be `filledClose`. Let the length of the string be `length`. If `length` is odd, there is no solution. If `length / 2 < filledOpen`, there is no solution. If `length / 2 < filledClose`, there is no solution. Now fill the first `length / 2 - filledOpen` question marks with `(`, and the rest with `)`. If the result string is a regular bracket string, there is a solution. Otherwise, there is no solution.

We prove that the above approach is correct, that is if there is a solution, the construction we provided is a solution.

A solution is described as an array of `(` and `)` characters to be filled sequentially from left to right into the string. The length of a solution must always be equal to the number of `?` characters present in the string.

We notice that all solutions are permutations of each other because the number of `(` characters to be filled and the number of `)` characters to be filled are both fixed. If we sort any arbitrary solution, we get our construction. We will prove that for every regular bracket string, if we swap two characters, not necessarily adjacent, where the left character is `)` and the right character is `(`, the resulting string is also a regular bracket string. Then it follows that for an arbitray solution, if we swap two characters, not necessarily adjacent, where the left character is `)` and the right character is `(`, we also get a valid solution. And since there are a lot of sorting algorithms that only swap inversions, it follows that when we sort an arbitrary solution, we also get a valid solution and thus, our construction is a valid solution. In [`FillInTheBlanks.v`](../theories/FillInTheBlanks.v), we use the selection sort algorithm. But it is also possible to use bubble sort, quick sort and other algorithms, as long as they only swap inversions. [Check out this file for the correctness proof.](./SelectionSort.md)

Now, we prove for a regular bracket string of the form `a = s1 + ")" + s2 + "(" + s3`, `b = s1 + "(" + s2 + ")" + s3` is also a regular bracket string. We will use `balanceFactorBasedDefinition` as it is more convenient. First, `b` already satisfies the first condition of `balanceFactorBasedDefinition` as it is a permutation of `a`. To prove that `b` satisfies the second definition, we need to consider several cases.

- The prefix `s` is a prefix of `s1`. This means `s` is a prefix of `a`, and as `a` is a regular bracket string, `countOpen(s) >= countClose(s)`.
- The prefix `s` is equal to `s1 + "(" + s'`, where `s'` is a prefix of `s2`. We have `s1 + ")" + s'` is a prefix of `a`, therefore `countOpen(s1) + countOpen(s') >= countClose(s1) + countClose(s') + 1`. To prove `countOpen(s) >= countClose(s)`, we prove `countOpen(s1) + countOpen(s') + 1 >= countClose(s1) + countClose(s')`. This is true because `countOpen(s1) + countOpen(s') + 1 >= countClose(s1) + countClose(s') + 2 >= countClose(s1) + countClose(s')`.
- The prefix `s` is equal to `s1 + "(" + s2 + ")" + s'`, where `s'` is a prefix of `s3`. We have `s1 + ")" + s2 + "(" + s'` is a prefix of `a`, therefore `countOpen(s1) + countOpen(s2) + countOpen(s') + 1 >= countClose(s1) + countClose(s2) + countClose(s') + 1`. From this, we can conclude that `countOpen(s) >= countClose(s)`, since if we expand the two sides, we get the same inequality as the previous step.

With this result, we can prove the next result.

**There is also a quick way to check if there are two separate ways to replace the question marks** (not proved yet)

Problem link: https://codeforces.com/contest/1709/problem/C

To check, we fill in the question marks according to the construction described in the previous result. But then we swap the last question mark filled with `(` and the first question mark filled with `)` and then check if the resulting string is a regular bracket string.

As described above, a solution is an array of characters to be filled sequentially from left to right into the string. Now we have two arbitrary solutions, `witness1` and `witness2`. These two solutions are different. We perform these preprocessing steps:

- If `witness1` is already equal to our construction, that is, we fill the first several question marks with `(` and the rest with `)`, don't do anything.
- Otherwise, swap `witness1` and `witness2` then replace `witness1` with our construction.

After these preprocessing steps, `witness1` and `witness2` are still two distinct valid solutions.

`witness1` has the form `((((...())))...)`. We can decompose `witness1` into two segments: the first segment filled with `(` and the second segment filled with `)`. While `witness2` has an arbitrary shape, we will still split it into two segments, the first segment with length equal to the first segment of `witness1` and the second segment with length equal to the second segment of `witness1`. And we will apply this decomposition to any other witness that we create.

As `witness1` and `witness2` are different, there is at least one character that is different.

There are two cases.
- The different character is in the first segment. In `witness1`, the character is `(`. In `witness2`, the character is `)`. We have no information about other characters in `witness2`. In order to proceed, we create another witness that is easier to inspect. We keep the different character, but for the other characters, we erase them and then fill them according to our construction.

  Let's take the string `(????)`. And for example, our `witness1` is `(())`, and our `witness2` is `()()`. The first different character is the second character in `witness2`. Let's apply `witness2` to the string, we then get `(()())`. Now, let's empty all the characters except the different character. We then get `(?)??)`. And then we can fill the question marks again with our construction and get a new witness that is easier to inspect.

  Let's call the new witness `witness3`. There is already a `)` residing in the first segment. Because of the way we fill the other characters, there is also a `(` residing in the second segment.

- The different character is in the second segment. Similarly, we create a new witness `witness3` where there is a `)` residing in the first segment and a `(` residing in the second segment.

Let's take a look at `witness3` again. `witness3` looks something like this:

```
                  a ( in segment 2
----first------   |
((((((()((((((()))())))))
       |       --second--
       a ) in segment 1
```

We perform these steps to transform `witness3` into the witness checked by the problem's solution.

- If the `)` in segment 1 is at the end of the segment, we need to do nothing. Otherwise, we swap the `)` in segment 1 with the character at the end of segment 1, which is guaranteed to be `(`. The witness remains a valid witness.
- If the `(` in segment 2 is at the beginning of the segment, we need to do nothing. Otherwise, we swap the character at the beginning of segment 2, which is guaranteed to be `)`, with the `(` in segment 2. The witness remains a valid witness.
