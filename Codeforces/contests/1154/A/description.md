## Codeforces 1154A - Restoring Three Numbers

### Source

https://codeforces.com/problemset/problem/1154/A

### Summary

#### Problem

There are 3 secret positive integers a, b, c. You're given a permutation of [a + b, a + c, b + c, a + b + c]. You have to find three numbers a, b, c (in any order) that satisfy the constraints.

#### Algorithm

The sum of all the numbers in the permutations is `3 * (a + b + c)`. Now we have the value of `a + b + c`. Let's call the sum s. For each element x of the permutation of [a + b, a + c, b + c, a + b + c], we replace the element with `s - x`. After that, we are left with a list of 4 elements with exactly 1 zero. Remove that zero and we have the result.

#### Proof

The code can be found at [`restore_three_numbers.v`](./restore_three_numbers.v).
