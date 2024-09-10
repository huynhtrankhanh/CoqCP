# Disjoint Set Union

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

Now that we have a scoring function, here are two rewrite rules that don't make the score worse.

**Rewrite rule 1:** `Unite Unit (Unite a b)` ⟶ `Unite (Unite a b) Unit`

- This rewrite rule doesn't change the score.

**Rewrite rule 2:** If a ≥ d, `Unite (Unite a b) (Unite c d)` ⟶ `Unite (Unite (Unite a b) c) d`

- The score for the left hand side is: `subtreeSum (Unite a b) + subtreeSum (Unite c d) + treeScore (Unite a b) + treeScore (Unite c d) = subtreeSum a + subtreeSum b + subtreeSum c + subtreeSum d + subtreeSum a + subtreeSum b + treeScore a + treeScore b + subtreeSum c + subtreeSum d + treeScore c + treeScore d = 2 * subtreeSum a + 2 * subtreeSum b + 2 * subtreeSum c + 2 * subtreeSum d + treeScore a + treeScore b + treeScore c + treeScore d`
- The score for the right hand side is:
