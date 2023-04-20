# Repeat and compare
You are given two strings \$a\$ and \$b\$ consisting of characters from a to z in lowercase. Let \$n\$ be the length of \$a\$. Let \$m\$ be the length of \$b\$. Let \$a'\$ be the string \$a\$ repeated \$m\$ times. Let \$b'\$ be the string \$b\$ repeated \$n\$ times. Check whether \$a'\$ is lexicographically less than \$b'\$.

Approach: check if \$a + b < b + a\$, where \$+\$ denotes concatenation.

Proof:

Lexicographical less (\$<\$) satisfies the trichotomy condition. For all strings \$a\$ and \$b\$, exactly one of three things is true: \$a < b\$, \$b < a\$ and \$a = b\$.

When we say \$m \times a\$, we mean repeat string \$a\$ \$m\$ times. When we say \$|a|\$, we mean the length of string \$a\$.

We will prove two things:
- \$a + b < b + a \rightarrow |b| \times a < |a| \times b\$
- \$a + b = b + a \rightarrow |b| \times a = |a| \times b\$

Before proceeding, here is an explanation of how \$a + b < b + a \leftrightarrow |b| \times a < |a| \times b\$ follows from the two facts above.
