## Codeforces 4A - Watermelon

### Source

https://codeforces.com/problemset/problem/4/A

### Summary

#### Problem

You are given a nonnegative integer x. Check if there exist two positive even integers a and b such that x = a + b.

#### Algorithm

The algorithm is given by the `is_division_possible` predicate.

#### Proof

The statement that is proven is that `is_division_possible` outputs `true` if and only if two weights exists that form a valid division of the watermelon.

There exists a valid division if and only if the total weight is not less than 4 and is an even number.

We split the statement into two parts.

-   If there exist two positive even integers a and b such a that x = a + b then x is not less than 4 and is an even number

    Because a is positive, 1 <= a. We consider two cases: a = 1 and 1 < a. As 1 is an odd number, a can't be equal to 1. Therefore 1 < a.

    Similarly, 1 < b. Therefore, we have 2 <= a and 2 <= b, which means 4 <= a + b = x.

    As a and b are even, a + b is even and therefore x is even.

-   If x is not less than 4 and is an even number then there exist two positive even integers a and b such a that x = a + b

    We pick a = 2 and b = x - 2. We will show both numbers are positive and even.

    First, 2 is an even and positive number, therefore a is even and positive.

    Second, as x is even and 2 is even, x - 2 is even and therefore b is even. Also as 4 <= a + b and a = 2, we have 2 <= b. Therefore b is positive.

We now proved our solution is correct. The code can be found at [`watermelon.v`](./watermelon.v).
