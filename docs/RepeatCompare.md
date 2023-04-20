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
  + Prove \$a + b < b + a \rightarrow |b| \times a < |a| \times b\$

    This is one of the two facts we will prove.
  + Prove \$|b| \times a < |a| \times b \rightarrow a + b < b + a\$

    We already have \$a + b < b + a\$. Great.
- If \$a + b = b + a\$:
  + Prove \$a + b < b + a \rightarrow |b| \times a < |a| \times b\$

    As \$a + b < b + a\$ is false, the whole statement is true.
  + Prove \$|b| \times a < |a| \times b \rightarrow a + b < b + a\$

    From \$a + b = b + a \rightarrow |b| \times a = |a| \times b\$, we have \$|b| \times a = |a| \times b\$. Therefore \$|b| \times a < |a| \times b\$ is false and thus the whole statement is true.
- If \$b + a < a + b\$:
  + Prove \$a + b < b + a \rightarrow |b| \times a < |a| \times b\$

    As \$a + b < b + a\$ is false, the whole statement is true.
  + Prove \$|b| \times a < |a| \times b \rightarrow a + b < b + a\$

    By substituting variables in the first fact, we have \$b + a < a + b \rightarrow |a| \times b < |b| \times a\$. From there we conclude \$|b| \times a < |a| \times b\$ is false, thus the whole statement is true.

Now we can start proving the two facts.
