From stdpp Require Import numbers list.
From CoqCP Require Import Options.

Inductive Result :=
  | Variables (a b c : nat)
  | Insufficient.

Inductive VariableIndex :=
  | Variable1
  | Variable2
  | Variable3.

Inductive Instruction :=
  | Increment (variable : VariableIndex)
  | LiteralSet (variable : VariableIndex) (x : nat)
  | SetVariable (destination from : VariableIndex)
  | Random (variable : VariableIndex)
  | Loop (times : nat) (instruction : Instruction)
  | LoopVariable (variable : VariableIndex) (instruction : Instruction)
  | Chain (instruction1 instruction2 : Instruction).

Definition choice (a b c : nat) (index : VariableIndex) :=
  match index with
  | Variable1 => a
  | Variable2 => b
  | Variable3 => c
  end.

Inductive reduce : Instruction -> nat -> nat -> nat -> Result -> list bool -> list bool -> Prop :=
  | reduce_Increment1 a b c l : reduce (Increment Variable1) a b c (Variables (S a) b c) l l
  | reduce_Increment2 a b c l : reduce (Increment Variable2) a b c (Variables a (S b) c) l l
  | reduce_Increment3 a b c l : reduce (Increment Variable3) a b c (Variables a b (S c)) l l
  | reduce_LiteralSet1 a b c l x : reduce (LiteralSet Variable1 x) a b c (Variables x b c) l l
  | reduce_LiteralSet2 a b c l x : reduce (LiteralSet Variable2 x) a b c (Variables a x c) l l
  | reduce_LiteralSet3 a b c l x : reduce (LiteralSet Variable3 x) a b c (Variables a b x) l l
  | reduce_Set1 a b c l x : reduce (SetVariable Variable1 x) a b c (Variables (choice a b c x) b c) l l
  | reduce_Set2 a b c l x : reduce (SetVariable Variable2 x) a b c (Variables a (choice a b c x) c) l l
  | reduce_Set3 a b c l x : reduce (SetVariable Variable3 x) a b c (Variables a b (choice a b c x)) l l
  | reduce_RandomInsufficient a b c x : reduce (Random x) a b c Insufficient [] []
  | reduce_Random1False a b c tail : reduce (Random Variable1) a b c (Variables 0 b c) (false::tail) tail
  | reduce_Random1True a b c tail : reduce (Random Variable1) a b c (Variables 1 b c) (true::tail) tail
  | reduce_Random2False a b c tail : reduce (Random Variable2) a b c (Variables a 0 c) (false::tail) tail
  | reduce_Random2True a b c tail : reduce (Random Variable2) a b c (Variables a 1 c) (true::tail) tail
  | reduce_Random3False a b c tail : reduce (Random Variable3) a b c (Variables a b 0) (false::tail) tail
  | reduce_Random3True a b c tail : reduce (Random Variable3) a b c (Variables a b 1) (true::tail) tail
  | reduce_ChainDie a b c i1 i2 l1 l2 (hDie : reduce i1 a b c Insufficient l1 l2) : reduce (Chain i1 i2) a b c Insufficient l1 l2
  | reduce_ChainLive a b c i1 i2 l1 l2 l3 a1 b1 c1 bag (hLive : reduce i1 a b c (Variables a1 b1 c1) l1 l2) (hNext : reduce i2 a1 b1 c1 bag l2 l3) : reduce (Chain i1 i2) a b c bag l1 l3
  | reduce_ZeroLoop a b c l i : reduce (Loop 0 i) a b c (Variables a b c) l l
  | reduce_SuccLoopDie a b c i count l1 l2 (hDie : reduce i a b c Insufficient l1 l2) : reduce (Loop (S count) i) a b c Insufficient l1 l2
  | reduce_SuccLoopLive a b c i count l1 l2 l3 a1 b1 c1 bag (hLive : reduce i a b c (Variables a1 b1 c1) l1 l2) (hNext : reduce (Loop count i) a1 b1 c1 bag l2 l3) : reduce (Loop (S count) i) a b c bag l1 l3
  | reduce_LoopVariable a b c i index bag l1 l2 (hLiteral : reduce (Loop (choice a b c index) i) a b c bag l1 l2) : reduce (LoopVariable index i) a b c bag l1 l2.
