# Disjoint set union

**Problem statement:** Given the smart contract [`DisjointSetUnion.js`](../programs/DisjointSetUnion.js), find a way to get the most money from the contract.

Proof strategy: we model actions as a tree.

```coq
Inductive Tree :=
| Unit
| Unite (x y : Tree).
```

We can then calculate the score for a tree.

```coq
Fixpoint subtreeSum (x : Tree) :=
  match x with
  | Unit => 1
  | Unite a b => subtreeSum a + subtreeSum b
  end.

Fixpoint treeScore (x : Tree) :=
  match x with
  | Unit => 0
  | Unite a b => subtreeSum a + subtreeSum b + treeScore a + treeScore b
  end.
```

Now that we have a scoring function, here are three rewrite rules that don't make the score worse.

**Rewrite rule 1:** Unite Unit (Unite a b) ⟶ Unite (Unite a b) Unit

- This rewrite rule doesn't change the score.

**Rewrite rule 2:** If subtreeSum a ≥ subtreeSum d, Unite (Unite a b) (Unite c d) ⟶ Unite (Unite (Unite a b) c) d

- The score for the left hand side is: subtreeSum (Unite a b) + subtreeSum (Unite c d) + treeScore (Unite a b) + treeScore (Unite c d) = subtreeSum a + subtreeSum b + subtreeSum c + subtreeSum d + subtreeSum a + subtreeSum b + treeScore a + treeScore b + subtreeSum c + subtreeSum d + treeScore c + treeScore d = 2 \* subtreeSum a + 2 \* subtreeSum b + 2 \* subtreeSum c + 2 \* subtreeSum d + treeScore a + treeScore b + treeScore c + treeScore d
- The score for the right hand side is: 3 \* subtreeSum a + 3 \* subtreeSum b + 2 \* subtreeSum c + subtreeSum d + treeScore a + treeScore b + treeScore c + treeScore d ≥ 2 \* subtreeSum a + subtreeSum d + 3 \* subtreeSum b + 2 \* subtreeSum c + subtreeSum d = 2 \* subtreeSum a + 3 \* subtreeSum b + 2 \* subtreeSum c + 2 \* subtreeSum d
- This rule doesn't make the score worse.

**Rewrite rule 3:** If subtreeSum a < subtreeSum d, Unite (Unite a b) (Unite c d) ⟶ Unite (Unite (Unite d c) b) a

- The score for the left hand side is: 2 \* subtreeSum a + 2 \* subtreeSum b + 2 \* subtreeSum c + 2 \* subtreeSum d + treeScore a + treeScore b + treeScore c + treeScore d
- The score for the right hand side is 3 \* subtreeSum d + 3 \* subtreeSum c + 2 \* subtreeSum b + subtreeSum a + treeScore d + treeScore c + treeScore b + treeScore a > 2 \* subtreeSum d + subtreeSum a + 3 \* subtreeSum c + 2 \* subtreeSum b + subtreeSum a = 2 \* subtreeSum d + 3 \* subtreeSum c + 2 \* subtreeSum b + 2 \* subtreeSum a
- This rule doesn't make the score worse. This rule strictly increases the score.

**Termination:** We can apply the three rules repeatedly and eventually we will run out of subterms to replace.

To prove this, we need another scoring function solely for proving termination. Then, we have to prove that as we apply the rules, the score reduces.

```coq
Fixpoint encodeToList (x : Tree) : list bool :=
  match x with
  | Unit => [true]
  | Unite a b => encodeToList b ++ encodeToList a ++ [false]
  end.

Fixpoint listToNat (x : list bool) :=
  match x with
  | [] => 0
  | false :: rest => 2 * listToNat rest
  | true :: rest => 2 * listToNat rest + 1
  end.

Definition encodeToNat (x : Tree) := listToNat (encodeToList x).
```

To prove termination, we prove `encodeToNat` decreases as we rewrite.

**Rewrite rule 1:** Unite Unit (Unite a b) ⟶ Unite (Unite a b) Unit

Let's prove that encodeToNat decreases:

1. First, let's expand the encodeToNat function for the left side of the rule:
   encodeToNat(Unite Unit (Unite a b))
   = listToNat(encodeToList(Unite Unit (Unite a b)))
   = listToNat(encodeToList(Unite a b) ++ encodeToList(Unit) ++ [false])
   = listToNat(encodeToList(b) ++ encodeToList(a) ++ [false] ++ [true] ++ [false])

2. Now for the right side:
   encodeToNat(Unite (Unite a b) Unit)
   = listToNat(encodeToList(Unit) ++ encodeToList(Unite a b) ++ [false])
   = listToNat([true] ++ encodeToList(b) ++ encodeToList(a) ++ [false] ++ [false])

3. Comparing these, we see that the only difference is the position of [true]:
   Left: [...b...a...false, true, false]
   Right: [true, ...b...a...false, false]

4. In the listToNat function, each element's contribution to the final value is doubled for each position it is shifted right.

5. Therefore, moving [true] from the second-to-last position to the first position will decrease its contribution to the final value, thus decreasing the overall encodeToNat value.

Therefore, encodeToNat decreases for rewrite rule 1.

**Rewrite rule 2:** If subtreeSum a ≥ subtreeSum d, Unite (Unite a b) (Unite c d) ⟶ Unite (Unite (Unite a b) c) d

Let's prove that encodeToNat decreases:

1. First, let's expand the encodeToNat function for the left side of the rule:
   encodeToNat(Unite (Unite a b) (Unite c d))
   = listToNat(encodeToList(Unite c d) ++ encodeToList(Unite a b) ++ [false])
   = listToNat(encodeToList(d) ++ encodeToList(c) ++ [false] ++ encodeToList(b) ++ encodeToList(a) ++ [false] ++ [false])

2. Now for the right side:
   encodeToNat(Unite (Unite (Unite a b) c) d)
   = listToNat(encodeToList(d) ++ encodeToList(Unite (Unite a b) c) ++ [false])
   = listToNat(encodeToList(d) ++ encodeToList(c) ++ encodeToList(Unite a b) ++ [false] ++ [false])
   = listToNat(encodeToList(d) ++ encodeToList(c) ++ encodeToList(b) ++ encodeToList(a) ++ [false] ++ [false] ++ [false])

3. Comparing these, we see that the difference is the position of [false]:
   Left: [d, c, false, b, a, false, false]
   Right: [d, c, b, a, false, false, false]

**Rewrite rule 3:** We can't prove encodeToNat decreases here. But we can still resuscitate the argument, as the score strictly increases and we can prove a loose upper bound on the score. When we prove the upper bound on the score, we can conclude that the rewrite system terminates.

So the termination measure we use here is actually the pair `(subtreeSum x * subtreeSum x - treeScore x, encodeToNat x)`. We now prove `treeScore x <= subtreeSum x * subtreeSum x`.

We do induction on the tree.

- **Base case:** The tree is Unit. treeScore is 0, subtreeSum is 1.
- **Inductive step:** The tree is Unite a b. We assume treeScore a <= (subtreeSum a)^2, treeScore b <= (subtreeSum b)^2. Now, treeScore (Unite a b) = treeScore a + treeScore b + subtreeSum a + subtreeSum b <= (subtreeSum a)^2 + (subtreeSum b)^2 + subtreeSum a + subtreeSum b. Now we prove for all a and b such that 1 <= a and 1 <= b, a^2 + b^2 + a + b <= (a + b)^2.
  We have (a^2 + b^2 + a + b) - (a + b)^2 = a + b - 2ab = a(1 - b) + b(1 - a). a is positive, 1 - b is nonpositive so a(1 - b) is nonpositive. Similarly b(1 - a) is nonpositive. Therefore a(1 - b) + b(1 - a) <= 0, so a^2 + b^2 + a + b <= (a + b)^2.
  Now, we can conclude treeScore (Unite a b) <= (subtreeSum (Unite a b))^2.

We've established an upper bound on the score. Now we conclude the rewrite system terminates.

Now we grab an arbitrary optimal tree, then we apply all the rewrite rules repeatedly. As the rules don't make the score worse, we get another tree which is also optimal, but all subterms of the tree can only be of the form `Unit` or `Unite (Unite a b) Unit`.
