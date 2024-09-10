# Disjoint Set Union

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
- This rule doesn't make the score worse.

**Termination:** We can apply the three rules repeatedly and eventually we will run out of subterms to replace.

To prove this, we need another scoring function solely for proving termination. Then, we have to prove that as we apply the rules, the score reduces.

```coq
Fixpoint uniteLeftCount (x : Tree) :=
  match x with
  | Unit => 0
  | Unite (Unite a _) _ => 1 + uniteLeftCount a
  end.

Fixpoint uniteCount (x : Tree) :=
  match x with
  | Unit => 0
  | Unite a b => 1 + uniteCount a + uniteCount b
  end.

Definition terminationMeasure (x : Tree) := uniteCount x - uniteLeftCount x.
```

The rewrite rules preserve `uniteCount`. For every tree x, `uniteLeftCount x <= uniteCount x`. Therefore, to prove termination, we prove `uniteLeftCount` increases as we rewrite.

**Rewrite rule 1:** Unite Unit (Unite a b) ⟶ Unite (Unite a b) Unit

- uniteLeftCount (Unite Unit (Unite a b)) = 0
- uniteLeftCount (Unite (Unite a b) Unit) = 1 + 1 + uniteLeftCount a
- uniteLeftCount increases

**Rewrite rule 2:** If subtreeSum a ≥ subtreeSum d, Unite (Unite a b) (Unite c d) ⟶ Unite (Unite (Unite a b) c) d

- uniteLeftCount (Unite (Unite a b) (Unite c d)) = 1 + 1 + uniteLeftCount a
- uniteLeftCount (Unite (Unite (Unite a b) c) d) = 1 + 1 + 1 + uniteLeftCount a
- uniteLeftCount increases

**Rewrite rule 3:** We can't prove uniteLeftCount increases here. But we can still resuscitate the argument, as the score strictly increases and we can prove a loose upper bound on the score. When we prove the upper bound on the score, we can conclude that the rewrite system terminates.

So the termination measure we use here is actually a pair `(uniteCount x - uniteLeftCount x, subtreeSum x * subtreeSum x - treeScore x)`. We now prove `treeScore x <= subtreeSum x * subtreeSum x`.

We do induction on the tree.
- **Base case:** The tree is Unit. treeScore is 0, subtreeSum is 1.
- **Induction step:** The tree is Unite a b. We assume treeScore a <= (subtreeSum a)^2, treeScore b <= (subtreeSum b)^2. Now, treeScore (Unite a b) = treeScore a + treeScore b + subtreeSum a + subtreeSum b <= (subtreeSum a)^2 + (subtreeSum b)^2 + subtreeSum a + subtreeSum b. Now we prove for all a and b such that 1 <= a and 1 <= b, a^2 + b^2 + a + b <= (a + b)^2.
  We have (a^2 + b^2 + a + b) - (a + b)^2 = a + b - 2ab = a(1 - b) + b(1 - a). a is positive, 1 - b is nonpositive so a(1 - b) is nonpositive. Similary b(1 - a) is nonpositive. Therefore a(1 - b) + b(1 - a) <= 0, so a^2 + b^2 + a + b <= (a + b)^2.
  Now, we can conclude treeScore (Unite a b) <= (subtreeSum (Unite a b))^2.

We've established an upper bound on the score. Now we conclude the rewrite system terminates.
