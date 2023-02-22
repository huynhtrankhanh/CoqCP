# Selection sort
**Note:** ChatGPT generated this file. I read through this proof and it looks correct. This proof is the same as the argument used in [`SelectionSortProperties.v`](../theories/SelectionSortProperties.v).

Selection sort is a simple sorting algorithm that works by repeatedly selecting the minimum element from the unsorted part of the array and swapping it with the first element of the unsorted part. The algorithm then moves the boundary of the unsorted part of the array one element to the right and repeats the process until the entire array is sorted.

To prove the correctness of selection sort, we need to show that the algorithm correctly sorts any input array. We can do this by showing two things:

Termination: The algorithm must terminate after a finite number of steps, and the output must be a sorted array.

Preservation of the loop invariant: At the beginning of each iteration of the outer loop, the subarray from index 0 to i-1 is already sorted, and all elements in the subarray are less than or equal to all elements in the unsorted subarray from index i to n-1.

Proof:

Termination: The outer loop of selection sort runs n-1 times, where n is the length of the input array. In each iteration, the algorithm selects the smallest element in the unsorted subarray and swaps it with the first element of the unsorted subarray. This places the smallest element in its correct position in the sorted subarray, and the unsorted subarray is reduced by one element. After n-1 iterations, the entire array is sorted, and the algorithm terminates. Therefore, the algorithm must terminate after a finite number of steps, and the output is a sorted array.

Preservation of the loop invariant: We need to show that at the beginning of each iteration of the outer loop, the subarray from index 0 to i-1 is already sorted, and all elements in the subarray are less than or equal to all elements in the unsorted subarray from index i to n-1.

At the beginning of the first iteration, the subarray from index 0 to i-1 is empty, so the loop invariant holds trivially. At the end of the first iteration, the smallest element in the entire array is in index 0, so the subarray from index 0 to i-1 is sorted, and all elements in the subarray are less than or equal to all elements in the unsorted subarray from index i to n-1.

At the beginning of the second iteration, the subarray from index 0 to i-1 contains the smallest element in the entire array, and the subarray from index i to n-1 is unsorted. Therefore, the loop invariant holds. After the second iteration, the two smallest elements in the array are in their correct positions, so the subarray from index 0 to i-1 is sorted, and all elements in the subarray are less than or equal to all elements in the unsorted subarray from index i to n-1.

We can continue this argument for all n-1 iterations, showing that at the beginning of each iteration, the loop invariant holds, and at the end of each iteration, the subarray from index 0 to i-1 is sorted, and all elements in the subarray are less than or equal to all elements in the unsorted subarray from index i to n-1.

Therefore, we have shown that selection sort correctly sorts any input array, and the proof is complete.
