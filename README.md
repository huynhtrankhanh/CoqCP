**You can't bluff a computer.**

This is a repository of formally verified competitive programming code. Formal verification is very important.

https://codeforces.com/blog/entry/111737

The problemsetters of this round accidentally [made an NP-complete problem](https://web.archive.org/web/20230125221257/https://codeforces.com/contest/1780/problem/C), and wrote a wrong greedy solution for it. The testers of this round guessed the same incorrect solution. The mistake was not caught during the review and testing phase. In the actual round, many folks also guessed the same incorrect solution. But a few smart folks proved the problem was NP-complete.

The problemsetters even wrote [an incorrect proof](https://codeforces.com/blog/entry/111737?#comment-996084) for the greedy solution. Community members said the proof doesn't make sense.

This mistake could have been avoided entirely if the folks responsible for the round had used formal verification. I'm learning it. Will you join me?

Dependencies: Only `coq-stdpp`.

Note: Whenever you create a new file, remember to import `Options` with the `From CoqCP Require Import Options.` command. Coq will then error if you apply a tactic when multiple goals are visible.

Documentation:

- [Internal imperative language](docs/InternalImperativeLanguage.md)
<hr>

- [Regular bracket strings](docs/RegularBracketString.md)
- [Selection sort](docs/SelectionSort.md)
- [Repeat and compare](docs/RepeatCompare.md)

Tasks:

- [Sorting subarrays](docs/SortingSubarrays.md)

**Why contribute?**

As a contributor, your contributions

- **Benefit you personally:**
  - You have a solid framework to reason about and solve competitive programming problems.
  - Your performance in programming contests leapfrogs significantly.
  - As an early adopter of formal verification, you have a competitive advantage in the labor market once formal verification gains widespread traction.
- **Benefit society at large:**
  - As more competitive programming techniques get documented through formal verification, this eases the learning curve for people interested in competitive programming.
  - Your contributions reduce the reliance on online judges for the verification of program correctness. Test cases on online judges can be not very stringent. Auxiliary programs facilitating the judging process can be wrong. But a formal proof is a sure guarantee of a program's correctness.
  - Contests become fairer as model solutions and auxiliary judging programs can be formally verified, thus reducing room for deadly errors in the contest preparation stage.
  - Your contributions will draw more attention to formal verification and aid its widespread adoption.
