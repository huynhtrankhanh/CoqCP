# Disjoint Set Union

```python3
import sys

# Read all input from stdin
input_data = sys.stdin.read()

# Remove all whitespace (spaces, tabs, newlines, etc.)
output_data = ''.join(input_data.split())

class Tree:
    def __init__(self, left=None, right=None):
        self.left = left
        self.right = right

def join(a: Tree = None, b: Tree = None) -> Tree:
    return Tree(left=a, right=b)

def norm_tree(x: Tree) -> Tree:
    if x is None:
        return x
    currentLeft = norm_tree(x.left)
    currentRight = norm_tree(x.right)
    if currentLeft is None:
        return join(currentRight, currentLeft)
    if currentRight is None:
        return x

    # Destructure left and right
    c1, c2 = currentLeft.left, currentLeft.right
    c3, c4 = currentRight.left, currentRight.right

    return norm_tree(join(norm_tree(join(norm_tree(join(c1, c2)), c3)), c4))

def tree_print(x: Tree = None) -> str:
    if x is None:
        return 'L'
    return f'J({tree_print(x.left)},{tree_print(x.right)})'

def parse_tree(s: str) -> Tree:
    # Base case: If we encounter 'L', return None (leaf node).
    if s == 'L':
        return None

    # Recursive case: Find the structure "J(..., ...)"
    if s.startswith('J(') and s.endswith(')'):
        # Remove the outer 'J(' and ')' to process the inside.
        inner = s[2:-1]

        # Split the string at the top level comma, not nested ones.
        # This works assuming the input format is correct.
        depth = 0
        split_idx = -1
        for i, char in enumerate(inner):
            if char == '(':
                depth += 1
            elif char == ')':
                depth -= 1
            elif char == ',' and depth == 0:
                split_idx = i
                break

        # Split the inner part into left and right subtree descriptions.
        left_str = inner[:split_idx]
        right_str = inner[split_idx + 1:]

        # Recursively parse the left and right subtrees.
        left_tree = parse_tree(left_str)
        right_tree = parse_tree(right_str)

        # Return a new Tree node with the parsed left and right children.
        return Tree(left=left_tree, right=right_tree)

    raise ValueError("Invalid tree string format")

print(tree_print(norm_tree(parse_tree(output_data))))
```
