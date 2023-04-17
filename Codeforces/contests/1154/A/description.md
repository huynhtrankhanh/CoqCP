## Codeforces 1154A - Restoring Three Numbers

### Source
https://codeforces.com/problemset/problem/1154/A

### Summary
#### Problem
There are 3 secret positive integers a, b, c. You're given a permutation of [a + b, a + c, b + c, a + b + c]. You have to find three numbers a, b, c (in any order) that satisfy the constraints.

#### Algorithm
The sum of all the numbers in the permutations is `3 * (a + b + c)`. Now we have the value of `a + b + c`. Let's call the sum s. For each element x of the permutation of [a + b, a + c, b + c, a + b + c], we replace the element with `s - x`. After that, we are left with a list of 4 elements with exactly 1 zero. Remove that zero and we have the result.

#### Proof
The theorem `solution_is_correct` aims to prove that for any valid input `input_l`, the algorithm `restore_a_b_c` returns a valid answer. In other words, it proves that the algorithm successfully restores the three secret integers `a`, `b`, and `c` from the given input list.
The proof proceeds as follows:
1. First, the proof destructs the input list `l'` into its components: the list `l` and the integers `a`, `b`, and `c`. It also destructs the hypothesis `H`, which contains the constraints and the permutation of the input list.
2. The proof then unfolds the definition of `is_answer_valid`, `restore_a_b_c`, and `restore_a_b_c_aux`, focusing on their core logic.
3. A key step in the proof is to establish that the sum of the elements in the list `l` is equal to 3 times the sum of the secret integers `a`, `b`, and `c`. This is done using the lemma `sum_elements_lemma`. The proof then substitutes the result of `foldr Z.add 0 l` in the algorithm with `(a + b + c) * 3`.
4. Since the algorithm divides this sum by 3, it simplifies to `a + b + c`, which is the total sum of the secret integers.
Next, the proof introduces the `map_subtract_lemma`, which states that mapping the function `(fun x => a + b + c - x)` over the list `[a + b; a + c; b + c; a + b + c]` results in the list `[c; b; a; 0]`.
5. Using the `map_subtract_lemma` and the permutation hypothesis `H5`, the proof shows that the result of the `map` function in the algorithm is a permutation of `[c; b; a; 0]`.
6. The proof then focuses on the `filter` function in the algorithm, which removes the element `0` from the list `[c; b; a; 0]`, resulting in the list `[c; b; a]`. This is shown using the `Hfilter` assertion.
7. Finally, the proof establishes that the algorithm's output is a permutation of the list `[a; b; c]` by combining the results from the `map` and `filter` functions. This is done by rewriting the output using `Hmap` and `Hfilter`, and applying the `Permutation_rev` lemma.

In conclusion, the proof `solution_is_correct` demonstrates that the algorithm `restore_a_b_c` correctly restores the secret integers `a`, `b`, and `c` from the given input list, adhering to the problem constraints and requirements.
(Proof description by GPT-4)

We now proved our solution is correct. The code can be found at [`restore_three_numbers.v`](./restore_three_numbers.v).
