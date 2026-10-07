**You can't bluff a computer.**

[📹 **Watch a video of a proof in this repository**](<./0000-5399%20(1).mkv>)  
[🗒️ **Read the thesis report**](./ITCSIU21011_HuynhTranKhanh.pdf)  
[💻 **Read the instructions on how to run the compiler**](./docs/InternalImperativeLanguage.md)

This is a repository of formally verified competitive programming code. Formal verification is very important.

https://codeforces.com/blog/entry/111737

The problemsetters of this round accidentally [made an NP-complete problem](https://web.archive.org/web/20230125221257/https://codeforces.com/contest/1780/problem/C), and wrote a wrong greedy solution for it. The testers of this round guessed the same incorrect solution. The mistake was not caught during the review and testing phase. In the actual round, many folks also guessed the same incorrect solution. But a few smart folks proved the problem was NP-complete.

The problemsetters even wrote [an incorrect proof](https://codeforces.com/blog/entry/111737?#comment-996084) for the greedy solution. Community members said the proof doesn't make sense.

This mistake could have been avoided entirely if the folks responsible for the round had used formal verification. I'm learning it. Will you join me?

Toolchain: **Rocq 9.3.0**, **Rocq Stdlib 9.2.0**, and **stdpp 1.13.0**. Exact dependencies are recorded in [coqcp-toolchain.opam](coqcp-toolchain.opam). See [installation and proof-checking commands](docs/ProofCoverage.md).

Note: Whenever you create a new file, remember to import `Options` with the `From CoqCP Require Import Options.` command. Rocq will then error if you apply a tactic when multiple goals are visible.

Documentation:

- [Internal imperative language](docs/InternalImperativeLanguage.md)
- [Proof coverage and verification commands](docs/ProofCoverage.md)
- [End-to-end execution and interactive protocol contracts](docs/EndToEndVerification.md)
- [Adversarial checking of AI-generated programs and proofs](docs/AdversarialChecking.md)

<hr>

- [Regular bracket strings](docs/RegularBracketString.md)
- [Selection sort](docs/SelectionSort.md)
- [Repeat and compare](docs/RepeatCompare.md)
- [Disjoint set union](docs/DisjointSetUnion.md)
- [CSES 3305: K-th Highest Score](CSES/3305/README.md)
- [CSES 3228: Permuted Binary Strings](CSES/3228/README.md)
- [Codeforces 1770G: Koxia and Bracket (end-to-end verified)](Codeforces/contests/1770/G/README.md)

Tasks:

- [Sorting subarrays](docs/SortingSubarrays.md)
