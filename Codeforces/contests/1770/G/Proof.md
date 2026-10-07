# Correctness and complexity

The specification counts **position masks**: two choices of positions count separately even if they produce the same bracket string. It chooses the longest balanced retained subsequences and reduces their number modulo 998244353. It also specifies the generated entry point, initial storage, successful execution, exact decimal output, and complete consumption of LF-terminated input.

## Split at the global minimum

Write B[i] for the balance after i input characters, m for its global minimum, and p for the first position attaining m. If a balanced deletion mask deletes O opening and C closing brackets, total balance gives O-C=B[n]. Nonnegative retained balance at p requires at least -m deleted closing brackets, so its deletion count is

O+C = B[n]+2C >= B[n]-2m.

This bound is attainable: the prefix through p can be balanced by deleting only -m closing brackets, and the suffix can be balanced by deleting only B[n]-m opening brackets. Greedily deleting unmatched brackets supplies witnesses. At equality, all deleted closing brackets occur in the prefix and no opening bracket in that prefix is deleted. The retained balance at p is zero. Thus every optimum is uniquely a pair of optimal half masks, and every such pair is an optimum. Multiply their counts. Reverse the suffix and flip both bracket kinds to reduce its count to the same half problem.

`OptimalSplit.v` proves the lower bound, equality characterization, and minimum-cut properties. `FullCounting.v` proves the bijection and the product formula against the specification's positional masks. `MinimumScan.v` proves the actual input scan chooses the required cut.

## Count one half

Scan the half greedily, marking a closing bracket special when it creates a new minimum. Let j be the number of deleted closing brackets beyond the minimum deficit accumulated so far. Opening brackets leave j unchanged. Initially dp[0]=1.

For an ordinary closing bracket, retaining it leaves j unchanged and deleting it increases j by one:

    next[j] = dp[j] + dp[j-1], with dp[-1]=0.

For a special closing bracket, deleting it leaves j unchanged; retaining it decreases j by one and is allowed only when the old j is positive:

    next[j] = dp[j] + dp[j+1].

The final coefficient dp[0] counts exactly the optimal half masks. `HalfCounting.v` and `KoxiaPaths.v` prove this interpretation, including the moving balance origin used to classify special events.

## Accelerate the transitions

For k closing events containing t special events, an incoming state j>=t cannot cross the forbidden negative boundary. On these states the ordinary and special transitions multiply the generating polynomial by 1+x and 1+x^-1 respectively. Their combined unrestricted action is x^-t(1+x)^k. Write the input polynomial as L+x^t H, where L has only degrees below t. The contribution of H is therefore H(1+x)^k. Process L recursively through the two halves, then add the bulk contribution.

The coefficients of (1+x)^k are binomial coefficients, obtained from factorial and inverse-factorial tables. Convolution uses the radix-two NTT modulo the certified prime 998244353. The required roots and inverse transforms are proved correct. The generated convolution, leaf transitions, frame stores, traversal, preprocessing, and both complete solve calls are proved to execute successfully with valid addresses and correct coefficients. Saved arena blocks remain valid while nested subtrees execute.

`KoxiaPolynomial.v` proves the decomposition and convolution identity. The generated execution proof continues through `KoxiaNTTCorrect.v`, `KoxiaConvolutionCorrect.v`, `KoxiaVisitInvariant.v`, `KoxiaPreprocess.v`, and `KoxiaSolveExecution.v`. `KoxiaMainInitialization.v`, `KoxiaMainSegments.v`, and `KoxiaMainResult.v` establish table setup, the two input orientations, and the final modular product. `Candidate.v` composes these results with the scan and decimal printer into the frozen `required program` contract.

## Time and storage

A non-root interval receives a polynomial of length O(k), where k is that interval's event count. Its parent truncates the incoming polynomial below the parent's special-event count. Only ordinary events can increase the represented length, by at most one per event. The parent's special-event count plus the number of ordinary events in its left child is at most the parent's event count. Thus the polynomial entering either child has length at most the parent's event count plus one. Both children have lengths within one of half the parent, so this bound is O(k) for either child. The root starts with one coefficient.

Each bulk convolution consequently has O(k) input and output coefficients. Rounding its transform length to a power of two changes this by at most a factor of two. Three radix-two transforms and the pointwise product cost O(k log(k+2)). Other node work is O(k). Leaves have at most 32 events and cost O(k), since their entering polynomials also have bounded length. Hence

    T(k) <= T(floor(k/2)) + T(ceil(k/2)) + O(k log(k+2)),

which sums to O(k log²(k+2)): the total interval length at each depth is O(k), and there are O(log(k+2)) depths. Both halves together take O(n log²(n+2)). Scanning, factorial tables, and root-table entries take O(n); modular exponentiation has a fixed modulus and bounded exponent. The input reader's fixed-capacity buffer contributes a fixed initialization cost.

The solver tables and live saved polynomials use O(n) storage. Arena requirements along a balanced traversal path form a geometric sum. The implementation also reserves a fixed 500000-byte input buffer and 32 frames for the specified input limit. The kernel proves arena, frame, polynomial, and transform bounds. The time bound above is an algorithmic analysis; the framework's functional execution semantics do not measure elapsed time or instruction costs.

The proofs cover the generated Rocq actions. The TypeScript compiler, emitted C++ correspondence, POSIX runtime, and allocation success remain outside those semantics; native differential tests and compiler regressions check those parts.
