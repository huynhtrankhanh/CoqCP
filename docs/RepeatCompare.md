# Repeat and compare

You are given two strings \$a\$ and \$b\$ consisting of characters from a to z in lowercase. Let \$n\$ be the length of \$a\$. Let \$m\$ be the length of \$b\$. Let \$a'\$ be the string \$a\$ repeated \$m\$ times. Let \$b'\$ be the string \$b\$ repeated \$n\$ times. Check whether \$a'\$ is lexicographically less than \$b'\$.

Approach: check if \$a + b < b + a\$, where \$+\$ denotes concatenation.

Proof:

Source: https://codegolf.stackexchange.com/a/259989/

Lexicographical less (\$<\$) satisfies the trichotomy condition. For all strings \$a\$ and \$b\$, exactly one of three things is true: \$a < b\$, \$b < a\$ and \$a = b\$.

When we say \$m \times a\$, we mean repeat string \$a\$ \$m\$ times. When we say \$|a|\$, we mean the length of string \$a\$.

We will prove two things for all strings \$a\$ and \$b\$:

- \$a + b < b + a \rightarrow |b| \times a < |a| \times b\$
- \$a + b = b + a \rightarrow |b| \times a = |a| \times b\$

Before proceeding, here is an explanation of how \$a + b < b + a \leftrightarrow |b| \times a < |a| \times b\$ follows from the two facts above.

- If \$a + b < b + a\$:

  - Prove \$a + b < b + a \rightarrow |b| \times a < |a| \times b\$

    This is one of the two facts we will prove.

  - Prove \$|b| \times a < |a| \times b \rightarrow a + b < b + a\$

    We already have \$a + b < b + a\$. Great.

- If \$a + b = b + a\$:

  - Prove \$a + b < b + a \rightarrow |b| \times a < |a| \times b\$

    As \$a + b < b + a\$ is false, the whole statement is true.

  - Prove \$|b| \times a < |a| \times b \rightarrow a + b < b + a\$

    From \$a + b = b + a \rightarrow |b| \times a = |a| \times b\$, we have \$|b| \times a = |a| \times b\$. Therefore \$|b| \times a < |a| \times b\$ is false and thus the whole statement is true.

- If \$b + a < a + b\$:

  - Prove \$a + b < b + a \rightarrow |b| \times a < |a| \times b\$

    As \$a + b < b + a\$ is false, the whole statement is true.

  - Prove \$|b| \times a < |a| \times b \rightarrow a + b < b + a\$

    By substituting variables in the first fact, we have \$b + a < a + b \rightarrow |a| \times b < |b| \times a\$. From there we conclude \$|b| \times a < |a| \times b\$ is false, thus the whole statement is true.

Now we can start proving the two facts. We'll prove \$a + b < b + a \rightarrow |b| \times a < |a| \times b\$ first.

To prove this fact, we need to prove two intermediary lemmas: `repeatA` and `repeatB`.

`repeatA`: $$\forall a\forall b\forall m, 0 < m \rightarrow a + b < b + a \rightarrow m \times a + b < b + m \times a$$

This lemma can be proved by doing induction on \$m\$.

Base case: \$m = 1\$. Substituting \$m\$, we get \$a + b < b + a\$, which is already true.

Induction step: We already have \$m \times a + b < b + m \times a\$, now we have to prove \$(m + 1) \times a + b < b + (m + 1) \times a\$.

To pull this off, we add \$a\$ to the left of both sides of the induction hypothesis. We now have

$$a + m \times a + b < a + b + m \times a < b + a + m \times a$$

Now this is identical to $$(m + 1) \times a + b < b + (m + 1) \times a$$

`repeatB`: $$\forall a\forall b\forall m, 0 < m \rightarrow a + b < b + a \rightarrow a + m \times b < m \times b + a$$

Using a similar argument to the one used in `repeatA`, we can prove this lemma. In the inductive step, however, we need to add \$b\$ to the right of both sides of the induction hypothesis instead.

Both `repeatA` and `repeatB` have the precondition \$0 < m\$. Before proceeding further, we need to separately handle the cases where either \$a\$ or \$b\$ is an empty string.

- If \$a\$ is empty, \$a + b < b + a\$ turns into \$b < b\$, which is a false statement.
- Similarly, \$b\$ can't be empty.

Applying `repeatA` on \$a\$, \$b\$ and \$|b|\$, along with the fact that \$a + b < b + a\$, we have \$|b| \times a + b < b + |b| \times a\$.

Applying `repeatB` on \$|b| \times a\$, \$b\$ and \$|a|\$, along with the fact that \$|b| \times a + b < b + |b| \times a\$, we have \$|b| \times a + |a| \times b < |a| \times b + |b| \times a\$.

For the sake of contradiction, let's suppose \$|b| \times a = |a| \times b\$. We rewrite this into \$|b| \times a + |a| \times b < |a| \times b + |b| \times a\$ and get \$|b| \times a + |b| \times a < |b| \times a + |b| \times a\$. This is false.

Therefore, \$|b| \times a \ne |a| \times b\$.

As \$|b| \times a \ne |a| \times b\$ and \$|b| \times a\$ and \$|a| \times b\$ are of the same length, from \$|b| \times a + |a| \times b < |a| \times b + |b| \times a\$ we get \$|b| \times a < |a| \times b\$.

Now we prove \$a + b = b + a \rightarrow |b| \times a = |a| \times b\$.

We also need to prove these two facts:

`repeatAEqual`: $$\forall a\forall b\forall m, 0 < m \rightarrow a + b = b + a \rightarrow m \times a + b = b + m \times a$$

`repeatBEqual`: $$\forall a\forall b\forall m, 0 < m \rightarrow a + b = b + a \rightarrow a + m \times b = m \times b + a$$

We can use the same argument as the argument we used for `repeatA` and `repeatB`.

Before proceeding further, we consider two cases.

- If \$a\$ is empty, \$|b| \times a + |a| \times b = |a| \times b + |b| \times a\$ reduces to \$\text{“”} = \text{“”}\$, which is true.
- Similarly, if \$b\$ is empty then \$|b| \times a + |a| \times b = |a| \times b + |b| \times a\$ is true.

Now we only need to consider the case where both \$a\$ and \$b\$ are non-empty.

Applying `repeatAEqual` on \$a\$, \$b\$ and \$|b|\$, along with the fact that \$a + b = b + a\$, we have \$|b| \times a + b = b + |b| \times a\$.

Applying `repeatBEqual` on \$|b| \times a\$, \$b\$ and \$|a|\$, along with the fact that \$|b| \times a + b = b + |b| \times a\$, we have \$|b| \times a + |a| \times b = |a| \times b + |b| \times a\$.

Taking a prefix of length \$|a||b|\$ on both sides, we get \$|b| \times a = |a| \times b\$.

The result is proved in [`RepeatCompare.v`](../theories/RepeatCompare.v).
