Proof.
  destruct (Z.eq_dec h 0) as [->|Hh].
  { rewrite !Z.div_0_r; reflexivity. }
  rewrite <-smod_mod.
  pose proof (Z.mod_bound_or a b) as Hr.
  revert Hr; generalize (a mod b); clear a; intros r Hr.
  assert (Hq : Z.quot b 2 = h).
  { rewrite H; replace (2*h) with (h*2) by lia.
    apply Z.quot_mul; discriminate. }
  destruct (Z.lt_trichotomy h 0) as [Hneg|[Hzero|Hpos]]; try contradiction.
  - destruct (Z_lt_ge_dec h r) as [Hsmall|Hlarge].
    + assert (Hs : Z.smodulo r b = r).
      { replace r with (r-b*0) at 2 by lia.
        apply (Z.smod_diveq 0); rewrite Hq; right; right; lia. }
      assert (Hd : r/h = 0).
      { apply (proj2 (Z.div_small_iff r h Hh)); right; lia. }
      rewrite Hs, Hd; reflexivity.
    + assert (Hs : Z.smodulo r b = r-b).
      { replace (r-b) with (r-b*1) by lia.
        apply (Z.smod_diveq 1); rewrite Hq; right; right; lia. }
      assert (Hd : r/h = 1).
      { symmetry; apply (Z.div_unique r h 1 (r-h)); [right; lia|lia]. }
      assert (He : (r-b)/h = -1).
      { symmetry; apply (Z.div_unique (r-b) h (-1) (r-h)); [right; lia|lia]. }
      rewrite Hs, Hd, He; reflexivity.
  - destruct (Z_lt_ge_dec r h) as [Hsmall|Hlarge].
    + assert (Hs : Z.smodulo r b = r).
      { replace r with (r-b*0) at 2 by lia.
        apply (Z.smod_diveq 0); rewrite Hq; right; left; lia. }
      assert (Hd : r/h = 0).
      { apply (proj2 (Z.div_small_iff r h Hh)); left; lia. }
      rewrite Hs, Hd; reflexivity.
    + assert (Hs : Z.smodulo r b = r-b).
      { replace (r-b) with (r-b*1) by lia.
        apply (Z.smod_diveq 1); rewrite Hq; right; left; lia. }
      assert (Hd : r/h = 1).
      { symmetry; apply (Z.div_unique r h 1 (r-h)); [left; lia|lia]. }
      assert (He : (r-b)/h = -1).
      { symmetry; apply (Z.div_unique (r-b) h (-1) (r-h)); [left; lia|lia]. }
      rewrite Hs, Hd, He; reflexivity.
Qed.
