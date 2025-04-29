
# Value proposition of the thesis
In the field of smart contracts, audits are often performed to ensure the security and correctness of the code, and they have proven to be effective. But, the issue with audits is that they find issues rather than prove the absence of issues. Auditors are primarily focused on finding flaws, rather than finding out why the code is correct. This leads to a couple of issues. First, there is always a chance that the auditors can miss issues. This might be because they are simply not thorough, but there is also a fundamental fact at play: in a program, there are often many execution paths, and it is simply not possible to explore all of them. When a program has a flaw, sometimes the flaw is so well hidden that it can’t be found even after a thorough audit. Some rare, meandering path through the program can cause an unexpected bug. Second, the auditors can be malicious and intentionally leave out critical bugs. The fundamental problem with auditing is we have to trust that the auditors do their job properly. The promise of smart contracts is that any user can look at the code and determine whether the code can be trusted. But it is impractical to expect that there are many people with the time and resources to carry out a full audit of the smart contracts they interact with independently, and so they have to resort to trusting audits, and as auditors are people they can be malicious or incompetent, there can always be room for nasty bugs to happen.

The thesis is about the formal verification of Ethereum smart contracts. Formal verification is the process of ensuring the correctness of software by providing a mathematical description of the software, the mathematical properties that it must satisfy, and a mathematical proof of how the software satisfies these properties. It is fundamentally different from auditing in that auditing finds issues, but formal verification proves the absence of issues. The work needed to write the mathematical proof for the correctness of the software is labor intensive and requires significant expertise. However, the resulting proof is automatically checked by a computer program for logical correctness. The promise is that, once the work is done, a technically inclined person with some basic math and formal verification knowledge can:
* Run the computer program to check whether the proof is correct
* Manually inspect the specification to check whether the properties proven are what the person expect

This work is much less labor intensive than performing a full audit and does not require trusting the expert who wrote the proof of correctness. Formal verification, once widely adopted, can serve to strengthen the trustless nature of the blockchain and smart contracts.
# Contributions of the thesis
The thesis consists of a new programming language to write smart contracts in, a compiler to compile the programming language to both Coq and Solidity, and two example smart contracts and their proofs.

# Knapsack smart contract verification

**Problem Statement**:
Given a list of items $L = [(w_1, v_1), \dots, (w_n, v_n)]$ and weight limit $W$, find a subset $S \subseteq L$ maximizing $\sum_{(w,v) \in S} v$ such that $\sum_{(w,v) \in S} w \leq W$.

**Algorithm** (0/1 Knapsack - Recursive):
$$
\text{knapsack}(L, W) = 
\begin{cases} 
0 & \text{if } L = \emptyset \\
\text{knapsack}(L', W) & \text{if } w_1 > W \\
\max\left(\text{knapsack}(L', W), \ v_1 + \text{knapsack}(L', W - w_1)\right) & \text{otherwise}
\end{cases}
$$
where $L' = \text{tail}(L)$.

**Proof of Correctness**:

*We prove by induction that $\text{knapsack}(L, W)$ computes the maximum achievable value, and $\text{knapsack\_elements}(L, W)$ returns an optimal subset $S$.*

**Base Case** ($L = \emptyset$):
- No items to choose. Maximum value is 0, matching $\text{knapsack}(\emptyset, W) = 0$.
- $\text{knapsack\_elements}$ returns $\emptyset$, which trivially satisfies weight constraints.

**Inductive Step**:
Assume for all lists shorter than $L$, $\text{knapsack}$ and $\text{knapsack\_elements}$ work correctly.

**Case 1**: First item's weight $w_1 > W$
- Item cannot be included. Optimal solution is $\text{knapsack}(L', W)$.
- $\text{knapsack\_elements}$ skips item, correctness follows by IH.

**Case 2**: $w_1 \leq W$
- Two options: include or exclude the item.
- **Excluding**: Value = $\text{knapsack}(L', W)$
- **Including**: Value = $v_1 + \text{knapsack}(L', W - w_1)$
- $\text{knapsack}$ chooses $\max$ of both, ensuring optimality.
- $\text{knapsack\_elements}$ selects whichever option gives higher total value, validated by IH.

**Formal Properties**:
1. **Sublist Property**: $\text{knapsack\_elements}(L, W) \subseteq L$
   - *Proof*: By induction. Each recursive call either skips or includes the head item, maintaining the sublist relation.

2. **Value Optimality**: $\sum v_i = \text{knapsack}(L, W)$
   - *Proof*: Structural induction aligning the sum with the $\max$ choices.

3. **Weight Constraint**: $\sum w_i \leq W$
   - *Proof*: Induction with arithmetic validation on accumulated weights.

4. **Maximality**: $\text{knapsack}(L, W)$ is the maximum possible value.
   - *Proof*: Assume a better solution exists; contradicts IH by constructing a higher value subset for a sublist.

---

# Coq Proof Script Walkthrough

```coq
Lemma knapsackMax (l : list (nat * nat)) (limit : nat) :
  isMaximum (knapsack l limit) (fun x => exists choice,
    sublist choice l /\
    fold_right (fun x acc => snd x + acc) 0 choice = x /\
    fold_right (fun x acc => fst x + acc) 0 choice <= limit).
Proof.
  revert limit.
  induction l as [| head tail IH]. 
  { (* Base Case: l = [] *)
    intro a. constructor.
    - (* Existence: [] achieves 0 *)
      exists []. simpl. constructor; [easy | lia].
    - (* Maximality: Any other choice must be ≤ 0 *)
      intros b [choice [h1 [h2 h3]]].
      rewrite sublist_nil_r in h1. rewrite h1 in h2. simpl in h2.
      subst b. lia. }
  (* Inductive Step: l = head :: tail *)
  intro limit. constructor.
  - (* Existence: knapsack_elements is a valid choice *)
    exists (knapsack_elements (head :: tail) limit).
    constructor; [apply knapsackElementsSublist | 
                  apply knapsackElementsSum | 
                  apply knapsackElementsLimit].
  - (* Maximality: Any other choice's value ≤ knapsack l limit *)
    intros score [l1 [hl [hs hS]]].
    destruct head as [weight value].
    simpl. case_decide as h1.
    + (* Case: weight > limit *)
      pose proof IH limit as [_ IH_max].
      rewrite sublist_cons_r in hl.
      destruct hl as [hl | [l2 [hl hL]]].
      * (* Sublist is from tail *)
        apply IH_max. exists l1. auto.
      * (* Contradiction: chosen items include head but head's weight > limit *)
        rewrite hl, foldrSum11 in hS. lia.
    + (* Case: weight ≤ limit *)
      rewrite sublist_cons_r in hl.
      destruct hl as [hl | [l [hl hL]]].
      * (* Sublist is from tail *)
        pose proof IH limit as [IH_exists IH_max].
        apply IH_max. exists l1. auto.
      * (* Sublist includes head *)
        pose proof IH (limit - weight) as [IH_exists IH_max].
        rewrite hl, foldrSum9 in hs. rewrite hl, foldrSum11 in hS.
        epose proof bb (score - value) (ex_intro _ l (conj hL (conj _ _))). lia.
        Unshelve. { lia. } { lia. }
Qed.
```

**Line-by-Line Explanation**:

1. **Induction Setup**:
   - `revert limit. induction l as [| head tail IH].`  
     Generalize `limit` and induct on the list `l`.

2. **Base Case** (`l = []`):
   - `exists []`  
     The only sublist is empty, with total value 0.
   - `sublist_nil_r`  
     Any sublist of `[]` must be `[]`.
   - `simpl in h2. subst b. lia`  
     Simplifies hypotheses and concludes maximality via arithmetic.

3. **Inductive Case** (`l = head :: tail`):
   - `constructor`  
     Split proof into existence and maximality parts.

4. **Existence Part**:
   - `exists (knapsack_elements ...)`  
     Provide the sublist computed by `knapsack_elements` as the witness.
   - `apply knapsackElementsSublist`  
     Prove it's a sublist via prior lemma.
   - `apply knapsackElementsSum`  
     Total value matches `knapsack` via lemma.
   - `apply knapsackElementsLimit`  
     Weight constraint holds via lemma.

5. **Maximality Part**:
   - `intros score [l1 [hl [hs hS]]]`  
     Introduce a hypothetical better solution `l1`.
   - `destruct head as [weight value]`  
     Decompose the head item for case analysis.
   - `case_decide as h1`  
     Check if head's weight exceeds limit.

6. **Subcase 1: weight > limit**:
   - `rewrite sublist_cons_r in hl`  
     Analyze sublist structure.
   - `destruct hl`  
     Split into cases where `l1` is from tail or includes head.
   - `lia`  
     Discharge contradictions using arithmetic.

7. **Subcase 2: weight ≤ limit**:
   - Similar structure, but considers inclusion of head.
   - `pose proof IH (limit - weight) as [IH_exists IH_max].`  
     Adjust score for the inductive hypothesis.
   - `Unshelve. { lia. } { lia. }`
     Validate arithmetic conditions for the inductive step.

# Maximum withdrawal contract verification

### **Step-by-Step Explanation**

---

#### **1. Tree Structure**
**Definition:**  
A *tree* represents how sets are merged in the contract:  
- **`Unit`:** A single set (leaf node).  
- **`Unite(a, b)`:** Merges two subtrees `a` and `b` into one set.  

**Example:**  
`Unite(Unite(Unit, Unit), Unit)` represents merging two sets, then merging the result with another set.  

---

#### **2. `encodeToNat`**  
**Purpose:** Maps trees to natural numbers to enforce termination.  

**Encoding Process:**  
1. **`encodeToList`:** Converts a tree to a boolean list:  
   - `Unit` → `[true]`.  
   - `Unite(a, b)` → `encodeToList(b) ++ encodeToList(a) ++ [false]` (encode right subtree first).  
2. **`listToNat`:** Interprets the boolean list as a binary number:  
   - `[true, false]` → $1 \times 2^1 + 0 \times 2^0 = 2$.  

**Example:**  
- `Unite(Unit, Unit)` → `[true, true, false]` → $1 \times 2^2 + 1 \times 2^1 + 0 \times 2^0 = 6$.  

---

#### **3. `constructTree` is Optimal**  
**Definition:**  
```coq
Fixpoint constructTree (n : nat) :=
  match n with
  | O => Unit
  | S n => Unite (constructTree n) Unit
  end.
```  
**Structure:**  
- `constructTree(n)` nests `Unite` with `Unit` on the right.  
- Example: `constructTree(3) = Unite(Unite(Unite(Unit, Unit), Unit), Unit)`.  

**Optimality:**  
Maximizes `treeScore` by structuring unions to accumulate the largest possible sums.  

---

#### **4. Proving Optimality via Exchange Argument**  
**Goal:** Show any optimal tree can be transformed into `constructTree`.  

**Steps:**  
1. **Start with an arbitrary optimal tree.**  
2. **Apply rewrite rules** to reshape it into `constructTree` without lowering the score.  
3. **Argue equivalence:** If no transformations lower the score, the original tree must match `constructTree`.  

**Exchange Argument:**  
- A proof technique where we "exchange" parts of a solution to match a desired structure, proving equivalence in quality.  

---

#### **5. Rewrite Rules**  
Three rules to reshape trees while preserving/improving `treeScore`:  

##### **Rule 1: Swap `Unit` with a Subtree**  
**Transformation:**  
`Unite Unit (Unite a b) ⟶ Unite (Unite a b) Unit`  

**Effect:**  
- **Score:** Unchanged.  
- **`encodeToNat`:** Decreases (moving `true` left reduces binary value).  

**Example:**  
- Before: `encodeToNat(Unite Unit (Unite Unit Unit)) = 6`  
- After: `encodeToNat(Unite (Unite Unit Unit) Unit) = 5`  

##### **Rule 2: Reorganize Larger Subtrees**  
**Condition:** `subtreeSum(a) ≥ subtreeSum(d)`  
**Transformation:**  
`Unite (Unite a b) (Unite c d) ⟶ Unite (Unite (Unite a b) c) d`  

**Effect:**  
- **Score:** Increases or stays the same (prioritizes larger subtrees).  
- **`encodeToNat`:** Decreases (flattens structure).  

**Example:**  
- Before: `treeScore = 2a + 2b + 2c + 2d`  
- After: `treeScore = 3a + 3b + 2c + d` (≥ original).  

##### **Rule 3: Promote Smaller Subtrees**  
**Condition:** `subtreeSum(a) < subtreeSum(d)`  
**Transformation:**  
`Unite (Unite a b) (Unite c d) ⟶ Unite (Unite (Unite d c) b) a`  

**Effect:**  
- **Score:** Strictly increases (exploits smaller subtrees).  
- **`encodeToNat`:** May increase or decrease (unpredictable, but secondary).  

---

#### **6. Termination Proof**  
**Termination Measure:**  
Use the pair $(\text{leafCount}^2 - \text{score}, \text{encodeToNat})$.  

**Why It Works:**  
1. **Score ≤ leafCount²:**  
   - **Proof:** By induction, for any tree:  
     - Base: `Unit` has score 0 ≤ 1².  
     - Step: For `Unite a b`, `treeScore(a) ≤ (subtreeSum(a))²`, so total score ≤ $(\text{subtreeSum}(a) + \text{subtreeSum}(b))²$.  
   - Thus, $\text{leafCount}^2 - \text{score} ≥ 0$.  

2. **Lexicographic Ordering:**  
   - Rules 1/2 decrease $\text{leafCount}^2 - \text{score}$ or keep it constant while decreasing `encodeToNat`.  
   - Rule 3 strictly decreases $\text{leafCount}^2 - \text{score}$, even if `encodeToNat` increases.  

**Result:** The measure strictly decreases with each rule application, forcing termination.  

---

#### **7. Termination → `constructTree`**  
**Final State:**  
- No rules apply → tree is `constructTree(n)`.  
- **Reason:** `constructTree` cannot be rewritten further (all subtrees are `Unit` or nested `Unite`).  

---

#### **8. Calculating `constructTree` Score**  
**Formula:**  
For `constructTree(n)` with $n+1$ leaves:  
$$
\text{treeScore} = \frac{(n+1)(n+2)}{2} - 1
$$  

**Derivation:**  
- Each `Unite` adds the current subtree sum (which grows linearly).  
- Sum: $1 + 2 + 3 + \dots + n = \frac{n(n+1)}{2}$.  

**Example:**  
For `n=3`:  
$$
\text{treeScore} = \frac{4 \times 5}{2} - 1 = 10 - 1 = 9
$$  

---

By applying rewrite rules to reshape any tree into `constructTree`, we ensure maximum `treeScore`. The termination measure guarantees progress, and the exchange argument proves no better structure exists.

# Internal imperative language
The Internal Imperative Language is a specialized, low-level programming language designed with two primary goals: facilitating formal program verification using Coq and enabling platform-specific code generation. It achieves this by compiling a single source code into both a Coq file and either a Solidity file (for blockchain environments) or a C++ file (for competitive programming scenarios).

The language borrows heavily from JavaScript syntax but assigns unique semantics to the parsed Abstract Syntax Tree (AST). It emphasizes explicit control over data types (particularly integers), memory management (via global arrays), and execution flow. This design choice supports rigorous verification and predictable behavior in the target execution environments. This document provides a comprehensive overview of its syntax, semantics, compiler workflow, features, and underlying mechanisms based on the available documentation.

**2. Compiler and Workflow (`CoqCP`)**

The `CoqCP` compiler translates Internal Imperative Language source files into Coq and target platform code (Solidity or C++).

* **Prerequisites:** Requires Node.js and npm.
* **Setup:**
    1.  Navigate to the `compiler` directory.
    2.  Install dependencies: `npm install`
    3.  Compile the compiler: `npx tsc --noCheck` (generates JavaScript files in `dist`).
* **Usage Modes & Command Line Interface (CLI):**
    * **Blockchain Mode:** Generates Coq (`.v`) and Solidity (`.sol`) files.
        * Command: `node dist/cli --blockchain <coq_output.v> <solidity_output.sol> <input_file_1.js> [<input_file_2.js> ...]`
    * **Competitive Programming Mode:** Generates Coq (`.v`) and C++ (`.cpp`) files.
        * Command: `node dist/cli <coq_output.v> <cpp_output.cpp> <input_file_1.js> [<input_file_2.js> ...]`
    * **Watch Mode:** Add the `--watch` flag to either command to automatically recompile when input files change.
    * **JSON Configuration:** Compiler options can be specified in a JSON file.
        * Command: `node dist/cli ?json <path_to_config.json>`
        * JSON Schema:
            ```typescript
            type Config =
              | {
                  type: 'competitive'
                  inputs: string[] // Source file paths
                  coqOutput: string // Path for Coq output
                  cppOutput: string  // Path for C++ output
                }
              | {
                  type: 'blockchain'
                  inputs: string[] // Source file paths
                  coqOutput: string // Path for Coq output
                  solidityOutput: string // Path for Solidity output
                }
            ```
* **Compiler Development:** Run `npx tsc -w -p .` in the `compiler` directory for continuous compilation during development.

**3. Language Structure**

Source files define modules and consist of procedures and optional environment/module declarations.

* **Modules (`module`):**
    * Declaration: `module(ModuleName)` where `ModuleName` is a valid JavaScript identifier (not a string).
    * Naming: Each source file represents a module. If `module()` is declared, the module has that name.
    * Main Module: If a module declaration is omitted, the file defines the program's *main module*.
    * Uniqueness: A program cannot have two modules with the same name, nor can it have more than one main module.
* **Environment Block (`environment`):**
    * Purpose: Declares global, statically-sized arrays accessible within the module.
    * Syntax:
        ```javascript
        environment({
          arrayName1: array([type1, type2, ...], size1),
          arrayName2: array([type3], size2),
          // ...
        })
        ```
    * `arrayName`: The identifier for the global array.
    * `[type1, type2, ...]`: A list defining the structure of each array element. If it contains multiple types, the element is a tuple.
    * `size`: A literal integer specifying the fixed number of elements in the array. Must be a positive integer representable as `int64`.
    * Primitive Types: `int8`, `int16`, `int32`, `int64`, `bool`. Blockchain mode adds `address` and `int256`.
* **Procedure Blocks (`procedure`):**
    * Purpose: Define functions or subroutines within a module.
    * Syntax:
        ```javascript
        procedure('procedureName', { localVar1: type, /* ... */ }, () => {
          // Procedure body: sequence of instructions
        })
        ```
    * `procedureName`: A string literal naming the procedure.
    * `{ localVar1: type, ... }`: An object literal declaring local variables and their primitive types. Variables are initialized to `0` (numeric) or `false` (boolean) if not preset during a `call`.
    * `() => { ... }`: The function body containing the sequence of language instructions.
    * Entry Point: The procedure named `"main"` within the main (unnamed) module serves as the program's execution starting point. If no main module or no `"main"` procedure exists, the program compiles but does nothing upon execution.

**4. Data Types and Literals**

* **Primitive Types:**
    * Core: `int8`, `int16`, `int32`, `int64`, `bool`
    * Blockchain-only: `address`, `int256`
* **Number Literals:**
    * Syntax: Standard integer notation (e.g., `0`, `123`, `-42`).
    * Interpretation: Always parsed as `int64`.
    * Signedness: Treated as *unsigned* 64-bit integers by default in most operations (arithmetic, comparison). Negative literals are converted to their two's complement unsigned representation (e.g., `-1` becomes `0xFFFFFFFFFFFFFFFF`). Use signed-specific instructions (`sDivide`, `sLess`) for signed behavior.
* **String Literals:**
    * Syntax: Standard single or double quotes (e.g., `'hello'`, `"world"`).
    * Usage: Primarily for iteration using `range('string', (byteVar) => ...)`, which iterates over the UTF-8 *bytes* of the string.
    * Limitation: String iteration using `range` is *not supported* in Blockchain mode (results in invalid Solidity).
* **Boolean Literals:** `true`, `false`.

**5. Variables and State Management**

* **Local Variables:**
    * Scope: Confined to the procedure where they are declared.
    * Access: `get('variableName')` retrieves the value.
    * Modification: `set('variableName', value)` assigns a new value. The `value` must match the variable's declared type.
* **Global Arrays:**
    * Scope: Defined in the `environment` block, accessible throughout the module.
    * Element Access: `retrieve("arrayName", index)` returns the element (or tuple) at the given `index`. The `index` must be an `int64`.
    * Tuple Element Access: If an array element is a tuple, access individual components using a *literal number* index: `retrieve("arrayName", index)[0]`, `retrieve("arrayName", index)[1]`, etc.
    * Modification: `store("arrayName", index, [value1, value2, ...])` writes values to the element at the `index`. The `index` must be `int64`. The number and types of values in the list `[...]` must exactly match the declared tuple structure for the array elements.
* **Communication Array (Blockchain Mode Only):**
    * Purpose: A dedicated mechanism for passing data between contracts during an `invoke` call. It acts as both input (calldata) and output (return data). Physically, it's one of the module's global arrays designated during the `invoke`.
    * Size Query: `communicationSize()` returns the size (`int64`) of the data buffer passed to the current contract execution context (this might be less than or equal to the size of the underlying global array specified in the `invoke` call).
    * Read: `retrieve(index)` reads a single byte (`int8`) from the communication buffer at the specified `int64` index. Note the different signature compared to global array `retrieve`.
    * Write: `store(index, value)` writes a single byte (`int8` `value`) to the communication buffer at the specified `int64` `index`. Note the different signature compared to global array `store`.

**6. Operations and Expressions**

* **Arithmetic Operators:** `+`, `-`, `*`, `|` (bitwise OR), `^` (bitwise XOR), `&` (bitwise AND), `~` (bitwise NOT).
    * Behavior: Operate on numeric types. Default to *unsigned* wraparound arithmetic (modulo 2^N, where N is the bit width). No overflow exceptions. Operands must be of the same numeric type.
* **Division:**
    * Unsigned: `divide(x, y)`
    * Signed: `sDivide(x, y)` (Can overflow/trap, unlike other arithmetic).
    * Operands must be numeric and of the same type. Result type matches operand type.
* **Boolean Logic Operators:** `||` (logical OR), `&&` (logical AND), `!` (logical NOT). Operate on `bool` types.
* **Comparison:**
    * Equality: `==`, `!=`. Operands must be of the same type (numeric, `bool`, or `address`).
    * Less Than:
        * Unsigned: `less(x, y)`
        * Signed: `sLess(x, y)`
    * Operands must be numeric and of the same type. Returns `bool`.
* **Type Coercion:** Explicitly convert between types.
    * Commands: `coerceInt8`, `coerceInt16`, `coerceInt32`, `coerceInt64`, `coerceInt256` (Blockchain only).
    * Input: Can take any numeric type or `bool`.
    * Boolean Conversion: `true` becomes `1`, `false` becomes `0`.
    * Output: The specified integer type.

**7. Control Flow**

* **Conditional (`if`/`else`):**
    * Syntax: `if (condition) { /* true branch */ } else { /* false branch */ }`
    * `condition`: Must evaluate to `bool`.
    * Braces `{}`: Mandatory for both branches.
    * `else if`: Not directly supported; use nested `if` within the `else` block.
* **Looping (`range`):** The only looping construct.
    * **Numeric Iteration:**
        * Syntax: `range(endValue, (counter) => { /* loop body */ })`
        * `endValue`: An `int64` expression.
        * `counter`: An `int64` loop variable, implicitly declared. Takes values from `0` up to (but not including) `endValue`.
    * **String Iteration:**
        * Syntax: `range('stringLiteral', (byteVariable) => { /* loop body */ })`
        * `stringLiteral`: A literal string.
        * `byteVariable`: An `int8` loop variable, implicitly declared. Takes values of the successive UTF-8 bytes of the string.
        * Limitation: Not supported in Blockchain mode.
    * **Loop Control:**
        * `"break"`: (String literal) Immediately exits the innermost `range` loop.
        * `"continue"`: (String literal) Skips the rest of the current loop iteration and proceeds to the next one.

**8. Procedures and Modularity**

* **Intra-Module Call:**
    * Syntax: `call('procedureName', { presetVar1: value1, ... })`
    * Calls a procedure defined within the same module.
    * `presetVar`: Allows initializing local variables of the called procedure. Unspecified variables get default values (0/false). Preset values must type-match the variable declarations.
    * Return: Procedures do not return values explicitly. Communication happens via side effects on global arrays.
    * Recursion: Not allowed. Procedures must be defined textually before their first call site within the module.
* **Inter-Module Call:**
    * Syntax: `call(ModuleName, { targetArray1: 'currentArray1', ... }, 'procedureName', { presetVar1: value1, ... })`
    * `ModuleName`: Identifier of the target module (must be defined in another input file).
    * `{ targetArray: 'currentArray', ... }`: **Array Mapping.** This is crucial. It maps *every* global array declared in the `environment` of `ModuleName` to a corresponding array in the *current* module. The called procedure (`procedureName` in `ModuleName`) will operate on the arrays provided by the caller via this mapping.
    * Mapping Validation: Mapped arrays (`targetArray` and `currentArray`) must exist in their respective modules and must have *identical type signatures* (same number of element types, same types in the same order).
    * Procedure Call: Similar to intra-module calls regarding `procedureName` and `presetVar`s.

**9. Blockchain Mode Features**

These features are *only* available when compiling with the `--blockchain` flag.

* **Types:** `address` (20-byte Ethereum address), `int256` (256-bit integer).
* **Coercion:** `coerceInt256(value)`.
* **Transaction Context:**
    * `getSender()`: Returns the `address` of the transaction originator (`msg.sender`).
    * `getMoney()`: Returns the amount of wei (`int256`) sent with the transaction (`msg.value`).
* **Ether Transfer:**
    * `donate(recipientAddress, amountWei)`: Sends `amountWei` (an `int256`) to the `recipientAddress` (an `address`).
* **Contract Interaction (`invoke`):**
    * Syntax: `invoke(targetAddress, amountWei, 'arrayName', communicationLength)`
    * `targetAddress`: The `address` of the contract to call.
    * `amountWei`: The amount of wei (`int256`) to send with the call.
    * `'arrayName'`: The string name of a global array *in the current module*. This array **must** be declared as `array([int8], size)`.
    * `communicationLength`: An `int64` specifying how many bytes from the start of `'arrayName'` should be sent as calldata to the `targetAddress`.
    * Mechanism: The first `communicationLength` bytes of the specified `arrayName` are passed as calldata. The called contract receives this data via its own communication array interface (`communicationSize`, `retrieve`). When the called contract finishes, its communication array's contents (up to the size it was invoked with) are passed back as return data and overwrite the corresponding bytes in the caller's original `arrayName`.
* **Communication Array Interface:** See Section 5.

**10. Parsing and Abstract Syntax Tree (AST)**

* **Syntax Basis:** Leverages JavaScript syntax. Parsing likely uses a JS parser like Acorn.
* **AST Structure (`CoqCPAST`):** The parser converts source code into a structured tree representation defined by interfaces like `CoqCPAST`, `Environment`, `Procedure`, `Instruction`, `ValueType`, etc. (See initial documentation for the full Typescript definition).
* **Key AST Nodes:**
    * `Environment`: Holds `Map<string, ArrayDeclaration>`.
    * `Procedure`: Holds name, `Map<string, Variable>` (locals), `Instruction[]` (body).
    * `Instruction`: Encapsulates operations like `get`, `set`, `store`, `retrieve`, `range`, `condition`, `call`, `invoke`, arithmetic/logic ops, coercions, etc. Each instruction node stores its source code `Location`.
    * `ValueType`: Represents operands/results, can be `Literal`, `LocalBinder`, or another `Instruction`.
* **Location Tracking:** Every significant AST node contains `location` data (start/end line/column), essential for error reporting during validation.

**11. Typechecking and Validation (`validateAST`)**

This crucial phase runs after parsing and before code generation. It ensures the program is well-formed, type-safe, and adheres to language rules.

* **Input:** A list of topologically sorted `CoqCPAST` modules and the `blockchain` mode flag.
* **Process:** Iterates through modules and procedures, performing a Depth-First Search (`dfs`) type analysis on instruction bodies.
* **Checks Performed:**
    * **Type Compatibility:** Verifies operands for arithmetic, logical, and comparison operators/instructions match expected types (e.g., `+` needs same numeric types, `&&` needs booleans, `less` needs same numeric types).
    * **Instruction Signatures:** Ensures arguments passed to instructions (`store`, `retrieve`, `invoke`, `donate`, `coerce*`, `writeChar`, etc.) have the correct types and structure.
    * **Assignments:** `set('var', value)` requires `value`'s type to match `var`'s declared type. `store("array", index, [...])` requires the tuple `[...]` to match the array's element type signature.
    * **Control Flow:** `if` condition must be `bool`. `range` end value must be `int64` (or `string` if not blockchain).
    * **Scope & References:** Detects undefined variables, binders (loop counters), procedures, modules, and global arrays. Ensures `"break"`/`"continue"` are within `range`.
    * **Array Access:** Checks `retrieve(...)[idx]` where `idx` must be a literal number within the tuple bounds. Checks array indices (`retrieve`, `store`) are `int64`.
    * **Procedure Calls:** Validates existence of called procedures, type agreement of preset variables. For cross-module calls, rigorously checks the array mapping for completeness and type signature equality between mapped arrays.
    * **Mode Restrictions:** Enforces that blockchain-specific instructions/types are only used in blockchain mode, and vice-versa for restricted features like `readChar`/`writeChar`/string `range`.
    * **Literal Correctness:** Validates number literal format and `int64` range. Checks array lengths are positive.
    * **Structural Integrity:** Detects duplicate module/procedure names. (Cyclic dependencies checked earlier).
* **Error Reporting:** Generates a list of `ValidationError` objects upon failure, each containing error details and precise source `Location`.
* **Output:** An empty error list indicates success, allowing code generation. Otherwise, compilation halts, reporting the errors.

**12. Example Program Analysis**

**Example 1: Min-Heap Implementation**

```js
environment({
  // Global heap array (adjust capacity as needed)
  heap: array([int32], 100000),
  // Global heap size tracker (number of elements currently in the heap)
  heapSize: array([int32], 1),
})

// siftUp moves the element at the given index upward to restore the heap property.
procedure(
  'siftUp',
  {
    index: int32, // parameter: starting index
    currentIndex: int32, // local variable for current index
    parentIndex: int32, // local variable for parent's index
    temp: int32, // local temporary variable for swapping
  },
  () => {
    set('currentIndex', get('index'))
    range(30, (i) => {
      if (get('currentIndex') == coerceInt32(0)) {
        ;('break')
      }
      // Compute parent index as (currentIndex - 1) / 2 (using unsigned division)
      set(
        'parentIndex',
        divide(get('currentIndex') - coerceInt32(1), coerceInt32(2))
      )
      // If the current element is less than its parent, swap them.
      if (
        less(
          retrieve('heap', coerceInt64(get('currentIndex')))[0],
          retrieve('heap', coerceInt64(get('parentIndex')))[0]
        )
      ) {
        set('temp', retrieve('heap', coerceInt64(get('currentIndex')))[0])
        store('heap', coerceInt64(get('currentIndex')), [
          retrieve('heap', coerceInt64(get('parentIndex')))[0],
        ])
        store('heap', coerceInt64(get('parentIndex')), [get('temp')])
        set('currentIndex', get('parentIndex'))
      } else {
        ;('break')
      }
    })
  }
)

// siftDown moves the element at the given index downward to restore the heap property.
procedure(
  'siftDown',
  {
    index: int32, // parameter: starting index
    currentIndex: int32, // local variable for current index
    leftChild: int32, // local variable for left child index
    rightChild: int32, // local variable for right child index
    smallestIndex: int32, // local variable to track the smallest among current and children
    temp: int32, // local temporary variable for swapping
  },
  () => {
    set('currentIndex', get('index'))
    if (retrieve('heapSize', 0)[0] != coerceInt32(0)) {
      range(30, (i) => {
        // Calculate child indices
        set('leftChild', get('currentIndex') * coerceInt32(2) + coerceInt32(1))
        set('rightChild', get('currentIndex') * coerceInt32(2) + coerceInt32(2))
        // Assume current index is the smallest.
        set('smallestIndex', get('currentIndex'))
        // Check left child.
        if (less(get('leftChild'), retrieve('heapSize', 0)[0])) {
          if (
            less(
              retrieve('heap', coerceInt64(get('leftChild')))[0],
              retrieve('heap', coerceInt64(get('smallestIndex')))[0]
            )
          ) {
            set('smallestIndex', get('leftChild'))
          }
        }
        // Check right child.
        if (less(get('rightChild'), retrieve('heapSize', 0)[0])) {
          if (
            less(
              retrieve('heap', coerceInt64(get('rightChild')))[0],
              retrieve('heap', coerceInt64(get('smallestIndex')))[0]
            )
          ) {
            set('smallestIndex', get('rightChild'))
          }
        }
        // If the smallest is the current element, then the heap property holds.
        if (get('smallestIndex') == get('currentIndex')) {
          ;('break')
        }
        // Otherwise, swap the current element with the smallest child.
        set('temp', retrieve('heap', coerceInt64(get('currentIndex')))[0])
        store('heap', coerceInt64(get('currentIndex')), [
          retrieve('heap', coerceInt64(get('smallestIndex')))[0],
        ])
        store('heap', coerceInt64(get('smallestIndex')), [get('temp')])
        set('currentIndex', get('smallestIndex'))
      })
    }
  }
)

// insert adds a new element into the heap.
procedure(
  'insert',
  {
    value: int32, // parameter: the value to insert
    index: int32, // local variable for index where value is inserted
  },
  () => {
    // Place new value at the end of the heap.
    store('heap', coerceInt64(retrieve('heapSize', 0)[0]), [get('value')])
    // Increase the heap size.
    store('heapSize', 0, [retrieve('heapSize', 0)[0] + coerceInt32(1)])
    // Compute the index of the newly inserted element.
    set('index', retrieve('heapSize', 0)[0] - coerceInt32(1))
    // Restore the heap property.
    call('siftUp', { index: get('index') })
  }
)

// pop removes the minimum element (at the root) from the heap.
procedure(
  'pop',
  {
    index: int32, // local variable for index computations
    temp: int32, // local temporary variable for swapping
  },
  () => {
    if (retrieve('heapSize', 0)[0] != coerceInt32(0)) {
      // Set index to the last element.
      set('index', retrieve('heapSize', 0)[0] - coerceInt32(1))
      // Swap the root with the last element.
      set('temp', retrieve('heap', 0)[0])
      store('heap', 0, [retrieve('heap', coerceInt64(get('index')))[0]])
      store('heap', coerceInt64(get('index')), [get('temp')])
      // Decrement the heap size.
      store('heapSize', 0, [retrieve('heapSize', 0)[0] - coerceInt32(1)])
      // Restore the heap property from the root.
      call('siftDown', { index: coerceInt32(0) })
    }
  }
)

procedure('main', { current: int32, sum: int64 }, () => {
  range(divide(communicationSize(), 4), (i) => {
    set(
      'current',
      coerceInt32(retrieve(i * 4)) * coerceInt32(16777216) +
        coerceInt32(retrieve(i * 4 + 1)) * coerceInt32(65536) +
        coerceInt32(retrieve(i * 4 + 2)) * coerceInt32(256) +
        coerceInt32(retrieve(i * 4 + 3))
    )
    if (retrieve('heapSize', 0)[0] != coerceInt32(0)) {
      if (!less(get('current'), retrieve('heap', 0)[0])) {
        set(
          'sum',
          get('sum') + coerceInt64(get('current') - retrieve('heap', 0)[0])
        )
        call('pop', {})
        call('insert', { value: get('current') })
      }
      call('insert', { value: get('current') })
    }
  })
  store(0, coerceInt8(divide(get('sum'), coerceInt64(72057594037927936)))) // Byte 7 (most significant byte)
  store(
    1,
    coerceInt8(
      divide(get('sum'), coerceInt64(281474976710656)) % coerceInt64(256)
    )
  ) // Byte 6
  store(
    2,
    coerceInt8(
      divide(get('sum'), coerceInt64(1099511627776)) % coerceInt64(256)
    )
  ) // Byte 5
  store(
    3,
    coerceInt8(divide(get('sum'), coerceInt64(4294967296)) % coerceInt64(256))
  ) // Byte 4
  store(
    4,
    coerceInt8(divide(get('sum'), coerceInt64(16777216)) % coerceInt64(256))
  ) // Byte 3
  store(
    5,
    coerceInt8(divide(get('sum'), coerceInt64(65536)) % coerceInt64(256))
  ) // Byte 2
  store(6, coerceInt8(divide(get('sum'), coerceInt64(256)) % coerceInt64(256))) // Byte 1
  store(7, coerceInt8(get('sum') % coerceInt64(256))) // Byte 0 (least significant byte)
})
```

* **`environment`:**
    * `heap: array([int32], 100000)`: A large global array to store heap elements (as 32-bit integers).
    * `heapSize: array([int32], 1)`: A single-element array acting as a counter for the number of elements currently in the heap.
* **`procedure('siftUp', ...)`:**
    * Purpose: Restore heap property upwards from `index`.
    * Logic: Compares element at `currentIndex` with its parent (`(currentIndex - 1) / 2`). If the current element is smaller, swaps them and continues upwards by setting `currentIndex` to `parentIndex`. The `range(30, ...)` acts as a safety break (max depth). Uses `coerceInt32` and `coerceInt64` for type safety in calculations and array access. Uses `less` for unsigned comparison.
* **`procedure('siftDown', ...)`:**
    * Purpose: Restore heap property downwards from `index`.
    * Logic: Compares element at `currentIndex` with its left (`2*idx + 1`) and right (`2*idx + 2`) children. Finds the index of the smallest among the three (`smallestIndex`). If the smallest is not the current index, swaps them and continues downwards by setting `currentIndex` to `smallestIndex`. Checks children indices are within `heapSize`. The `range(30, ...)` acts as a safety break. Uses `less` for unsigned comparison. Handles the case where `heapSize` is 0 initially.
* **`procedure('insert', ...)`:**
    * Purpose: Add `value` to the heap.
    * Logic: Stores `value` at the current end of the heap (`heap[heapSize]`). Increments `heapSize`. Calls `siftUp` starting from the newly added element's index (`heapSize - 1`) to restore the heap property.
* **`procedure('pop', ...)`:**
    * Purpose: Remove and effectively return the minimum element (root). (Note: the language doesn't have return values, so the minimum is just removed).
    * Logic: If the heap is not empty, it swaps the root element (`heap[0]`) with the last element (`heap[heapSize - 1]`). Decrements `heapSize`. Calls `siftDown` starting from the root (`index: 0`) to restore the heap property.
* **`procedure('main', ...)`:**
    * Purpose: Reads 32-bit unsigned integers from the communication array (calldata), maintains a fixed-size min-heap (implicitly, by comparing with the current min and potentially replacing it), and calculates a running sum based on differences. Writes the final 64-bit sum back to the first 8 bytes of the communication array.
    * Calldata Reading: `range(divide(communicationSize(), 4), (i) => ...)` iterates over 4-byte chunks. Inside, it reconstructs a 32-bit integer (`current`) from 4 bytes read using `retrieve(idx)` and bit shifts/multiplication (effectively `byte0 * 2^24 + byte1 * 2^16 + ...`). Note the use of `coerceInt32` and `coerceInt64`.
    * Heap Logic: It maintains a min-heap implicitly. If the heap isn't empty (`heapSize != 0`), it compares the new `current` value with the heap's minimum (`retrieve('heap', 0)[0]`). If `current` is larger, it calculates the difference, adds it to `sum`, removes the old minimum (`call('pop', {})`), and inserts `current` (`call('insert', { value: get('current') })`). It then *always* inserts `current` again.
    * Result Writing: After processing all input, it takes the final 64-bit `sum` and writes it byte-by-byte into the first 8 indices of the communication array using `store(index, value)`. It extracts bytes using unsigned division (`divide`) and modulo (`%`, implemented via `a - divide(a, b) * b` if needed, though `%` might be available) by powers of 256. Note the use of `coerceInt8` before storing.

**Example 2: State Update and Contract Interaction**

```js
environment({
  current: array([int32], 1),
  count: array([int32], 1),
  scratchpad: array([int8], 1024),
})

procedure('main', { what: int32, absolute: address }, () => {
  // extract number from calldata
  set(
    'what',
    (coerceInt32(retrieve(0)) << coerceInt32(24)) +
      (coerceInt32(retrieve(1)) << coerceInt32(16)) +
      (coerceInt32(retrieve(2)) << coerceInt32(8)) +
      coerceInt32(retrieve(3))
  )

  if (retrieve('count', 0)[0] == coerceInt32(0)) {
    store('current', 0, [get('what')])
  }

  if (get('what') == retrieve('current', 0)[0]) {
    store('count', 0, [retrieve('count', 0)[0] + coerceInt32(1)])
  } else {
    store('count', 0, [retrieve('count', 0)[0] - coerceInt32(1)])
  }

  store(0, coerceInt8(retrieve('count', 0)[0] >> coerceInt32(24)))
  store(
    1,
    coerceInt8((retrieve('count', 0)[0] >> coerceInt32(16)) & coerceInt32(255))
  )
  store(
    2,
    coerceInt8((retrieve('count', 0)[0] >> coerceInt32(8)) & coerceInt32(255))
  )
  divide(3, 5)
  sDivide(3, 5)
  store(3, coerceInt8(retrieve('count', 0)[0] & coerceInt32(255)))

  donate(get('absolute'), coerceInt256(2000))
  invoke(get('absolute'), coerceInt256(2000), 'scratchpad', coerceInt64(1024))
  invoke(getSender(), getMoney(), 'scratchpad', coerceInt64(1024))
  invoke(
    address(
      coerceInt8(0),
      coerceInt8(0),
      coerceInt8(0),
      coerceInt8(0),
      coerceInt8(0),
      coerceInt8(0),
      coerceInt8(0),
      coerceInt8(0),
      coerceInt8(0),
      coerceInt8(0),
      coerceInt8(0),
      coerceInt8(0),
      coerceInt8(0),
      coerceInt8(0),
      coerceInt8(0),
      coerceInt8(0),
      coerceInt8(0),
      coerceInt8(0),
      coerceInt8(0),
      coerceInt8(0)
    ),
    getMoney(),
    'scratchpad',
    coerceInt64(1024)
  )
})
```

* **`environment`:**
    * `current: array([int32], 1)`: Stores the current candidate value (e.g., for majority element).
    * `count: array([int32], 1)`: Stores the associated counter.
    * `scratchpad: array([int8], 1024)`: A buffer array, likely used for `invoke` calls.
* **`procedure('main', ...)`:**
    * Purpose: Reads a 32-bit integer from calldata, updates state variables (`current`, `count`) based on the Boyer-Moore majority vote algorithm, writes the `count` back to the communication array, and demonstrates various blockchain interactions.
    * Calldata Reading: Reads the first 4 bytes using `retrieve(0)` to `retrieve(3)` and reconstructs a 32-bit integer `what` using bit shifts (`<<`) and addition. Uses `coerceInt32`.
    * State Update Logic: Implements a step of the Boyer-Moore majority vote algorithm. If `count` is 0, the new `what` becomes the `current` candidate, and `count` becomes 1. If `what` matches `current`, `count` increments. Otherwise (`what` differs), `count` decrements.
    * Result Writing: Writes the final 32-bit `count` value back to the first 4 bytes of the communication array using bit shifts (`>>`) and bitwise AND (`&`) to extract bytes, followed by `coerceInt8` and `store`.
    * Blockchain Interactions:
        * `donate(get('absolute'), coerceInt256(2000))`: Sends 2000 wei to the address stored in the local variable `absolute` (which isn't initialized in the snippet, implying it might be preset via `call`).
        * `invoke(get('absolute'), coerceInt256(2000), 'scratchpad', coerceInt64(1024))`: Calls the contract at `absolute`, sending 2000 wei, and passing the `scratchpad` array (up to 1024 bytes) for communication.
        * `invoke(getSender(), getMoney(), 'scratchpad', coerceInt64(1024))`: Calls the contract that initiated the current transaction (`getSender()`), forwarding the originally sent wei (`getMoney()`), using `scratchpad` for communication.
        * `invoke(address(...), getMoney(), 'scratchpad', coerceInt64(1024))`: Calls address 0, forwarding `getMoney()`, using `scratchpad`. The `address(...)` constructor takes 20 `int8` values (explicitly zero here).

**13. Limitations**

* **Unsigned Default:** Arithmetic and comparisons are unsigned unless `sDivide`/`sLess` are used.
* **No 2D Arrays:** Requires manual flattening for multi-dimensional data.
* **Explicit Division/Comparison:** Uses `divide`/`sDivide`/`less`/`sLess` functions, not operators.
* **No Recursion:** Procedures cannot call themselves directly or indirectly.
* **Limited String Ops:** Primarily byte-wise iteration via `range` (unavailable in blockchain mode).
* **No Return Values:** Procedures communicate results via side effects on global or communication arrays.
* **Static Arrays:** Global array sizes are fixed at compile time.
* **Control Flow:** Only `if/else` and `range` loops available.

