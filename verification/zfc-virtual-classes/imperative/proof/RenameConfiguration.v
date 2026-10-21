From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash RenameStructure RenameLeaf RenameJoin RenameAtom RenamePush RenameNext.
From stdpp Require Import numbers list.
Module RenameConfiguration.
Import IndexExecution SipHashExecution RenameStructure.
Definition preserved (before after : Frame) :=
  nums after vardef_0__rename_mode = nums before vardef_0__rename_mode /\
  nums after vardef_0__rename_shift = nums before vardef_0__rename_shift /\
  nums after vardef_0__rename_arg = nums before vardef_0__rename_arg.
Lemma loaded f top root depth phase left_id tag a b : preserved f (RenameLeaf.loaded f top root depth phase left_id tag a b).
Proof. repeat split; reflexivity. Qed.
Lemma falsity f top root depth left_id : preserved f (RenameLeaf.false_state f top root depth left_id).
Proof. repeat split; reflexivity. Qed.
Lemma join f internstate top root depth phase left_id tag a b :
  preserved f (RenameJoin.result f internstate top root depth phase left_id tag a b).
Proof. repeat split; reflexivity. Qed.
Lemma atom f internstate top root depth left_id tag a b mapped_a mapped_b :
  preserved f (RenameAtom.result f internstate top root depth left_id tag a b mapped_a mapped_b).
Proof. repeat split; reflexivity. Qed.
Lemma push f pushed top root depth left_id tag a b : preserved f (RenamePush.result f pushed top root depth left_id tag a b).
Proof. repeat split; reflexivity. Qed.
Lemma next f pushed top root depth left_id tag a b : preserved f (RenameNext.result f pushed top root depth left_id tag a b).
Proof. repeat split; reflexivity. Qed.
End RenameConfiguration.
