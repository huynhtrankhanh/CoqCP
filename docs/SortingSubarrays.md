# Sorting subarrays
**Problem statement**

You are given an array A with length N. There are Q queries that you need to process. Each query i has two integers L[i] and R[i], and you need to sort the subarray A[L[i]...R[i]]. After processing all the queries, you need to output the value of A[K].

**Input**

The input consists of the following:

- The first line contains three integers N, K, and Q (1 <= N, Q <= 2 * 10^5, 1 <= K <= N), where N is the length of the array, K is the index of the element to output, and Q is the number of queries.

- The second line contains N integers A[1], A[2], ..., A[N] (1 <= A[i] <= 10^9), representing the elements of the array.

- Each of the next Q lines contains two integers L[i] and R[i] (1 <= L[i] <= R[i] <= N), representing a query.

**Output**

Output a single integer, which is the value of A[K] after processing all the queries.

Example

Input:
```
5 3 2
4 2 1 3 5
1 3
2 4
```

Output:
```
3
```

Explanation:

- After processing the first query, the array becomes [1, 2, 4, 3, 5].
- After processing the second query, the array becomes [1, 2, 3, 4, 5].
- The value of A[3] after processing all the queries is 3.

**Your job:** find out the solution to this problem and code a formally verified solution.
