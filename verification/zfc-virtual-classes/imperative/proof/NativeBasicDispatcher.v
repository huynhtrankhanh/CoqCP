From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash DecimalInput NativeState NativeSession CommandLoop NativeSimpleCommands NativeCommandBoundary
 NativeNamedBoundary NativeQueryCommands NativeMPBoundary NativeTheoremBoundary NativeGeneralizeBoundary
 LogicalNames LogicalHistory TokenByte ClassSetRefinement ClassAbstractRefinement HistoryRefinement
 CommandNameQuery RecallRefinement NameQueryRefinement ArityRefinement LookupClassRefinement.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeBasicDispatcher.
Import IndexExecution SipHashExecution.
Definition two opcode := opcode=1%nat \/ opcode=2%nat \/ opcode=3%nat \/ opcode=12%nat \/ opcode=18%nat.
Definition one opcode := opcode=4%nat \/ opcode=5%nat \/ opcode=6%nat \/ opcode=13%nat \/ opcode=19%nat.
Definition zero opcode := opcode=16%nat \/ opcode=17%nat.
Definition named opcode := opcode=9%nat \/ opcode=20%nat \/ opcode=23%nat.
Definition query opcode := opcode=10%nat \/ opcode=15%nat \/ opcode=21%nat \/ opcode=25%nat \/ opcode=26%nat.
Definition supported opcode := two opcode \/ one opcode \/ zero opcode \/ named opcode \/ query opcode.
Inductive form : Protocol.request -> Prop :=
| form_two opcode a b : two opcode -> form (Protocol.Req opcode [a;b] [])
| form_one opcode value : one opcode -> form (Protocol.Req opcode [value] [])
| form_zero opcode : zero opcode -> form (Protocol.Req opcode [] [])
| form_named opcode value name : named opcode -> form (Protocol.Req opcode [value] name)
| form_query opcode name : query opcode -> form (Protocol.Req opcode [] name).
Definition first opcode := List.hd 0 (decimalBytes opcode).
Definition rest request := List.tl (Protocol.request_bytes request).
(** Current-state sufficient arithmetic capacity. These are mathematical
    cardinalities and name-storage sizes, not execution assumptions. *)
Record resources (native:Machine) (logical:Protocol.state) (request:Protocol.request) : Prop := Resources {
 formula_room : Z.of_nat (length (Protocol.formulas logical))<=9223372036854775807;
 class_room : Z.of_nat (length (Protocol.classes logical))<maximum;
 history_room : Z.of_nat (length (Protocol.history logical))<maximum;
 binding_room : Z.of_nat (length (Protocol.bindings logical))<maximum;
 name_room : Z.of_nat (length (memory native arraydef_0__names)+length (Protocol.object_name request))<=maximum
}.
Lemma supported_bound opcode : supported opcode -> (1<=opcode<=26)%nat.
Proof. unfold supported,two,one,zero,named,query. intuition lia. Qed.
Lemma shape_form request : Protocol.shape request -> supported (Protocol.opcode request) -> form request.
Proof.
 destruct request as [opcode values name]. intros [Hwords Hshape] Hsupported.
 cbn [Protocol.opcode] in Hsupported.
 destruct Hsupported as [Htwo|[Hone|[Hzero|[Hnamed|Hquery]]]].
 - unfold two in Htwo. destruct Htwo as [->|[->|[->|[->| ->]]]];
   cbn [Protocol.arguments Protocol.object_name] in Hshape;
   destruct Hshape as [Hlength ->];destruct values as [|a [|b [|bad values]]];cbn [length] in Hlength;try lia;
   apply form_two;unfold two;auto.
 - unfold one in Hone. destruct Hone as [->|[->|[->|[->| ->]]]];
   cbn [Protocol.arguments Protocol.object_name] in Hshape;
   destruct Hshape as [Hlength ->];destruct values as [|value [|bad values]];cbn [length] in Hlength;try lia;
   apply form_one;unfold one;auto.
 - unfold zero in Hzero. destruct Hzero as [->| ->];cbn [Protocol.arguments Protocol.object_name] in Hshape;
   destruct Hshape as [-> ->];apply form_zero;unfold zero;auto.
 - unfold named in Hnamed. destruct Hnamed as [->|[->| ->]];
   cbn [Protocol.arguments Protocol.object_name] in Hshape;
   destruct Hshape as [Hlength Hname];destruct values as [|value [|bad values]];cbn [length] in Hlength;try lia;
   apply form_named;unfold named;auto.
 - unfold query in Hquery. destruct Hquery as [->|[->|[->|[->| ->]]]];
   cbn [Protocol.arguments Protocol.object_name] in Hshape;
   destruct Hshape as [-> Hname];apply form_query;unfold query;auto.
Qed.
Lemma join_prefix head fields : exists suffix,Protocol.join_tokens (head::fields)++[10]=head++suffix.
Proof. destruct fields as [|field fields];[exists [10];reflexivity|].
 exists (32::Protocol.join_tokens (field::fields)++[10]). cbn [Protocol.join_tokens]. now rewrite <-app_assoc. Qed.
Lemma request_prefix request : exists suffix,Protocol.request_bytes request=decimalBytes (Protocol.opcode request)++suffix.
Proof.
 destruct request as [opcode values name]. unfold Protocol.request_bytes;cbn [Protocol.opcode Protocol.arguments Protocol.object_name].
 let rec cases count index := lazymatch count with O=>idtac | S ?rest=>destruct index as [|index];[idtac|cases rest index] end in cases 27%nat opcode.
 all:apply join_prefix.
Qed.
Theorem request_encoding request : supported (Protocol.opcode request) ->
 Protocol.request_bytes request=first (Protocol.opcode request)::rest request /\ 0<=first (Protocol.opcode request)<256.
Proof.
 intro Hsupported. pose proof (supported_bound _ Hsupported) as Hbound.
 destruct (DecimalInput.decimal_word (Protocol.opcode request) ltac:(unfold maximum;lia)) as [_ [Hdigits Hlength]].
 destruct (request_prefix request) as [suffix Hprefix].
 destruct (decimalBytes (Protocol.opcode request)) as [|ch chars] eqn:Hdecimal;[cbn [length] in Hlength;lia|].
 inversion Hdigits as [|ch' chars' Hbyte Hrest];subst ch' chars'.
 unfold first,rest. rewrite Hdecimal,Hprefix. cbn [List.app List.hd List.tl]. split;[reflexivity|lia].
Qed.
Ltac opcode_digits := repeat first [progress change (decimalBytes 0%nat) with [48]|progress change (decimalBytes 1%nat) with [49]|progress change (decimalBytes 2%nat) with [50]|progress change (decimalBytes 3%nat) with [51]|progress change (decimalBytes 4%nat) with [52]|progress change (decimalBytes 5%nat) with [53]|progress change (decimalBytes 6%nat) with [54]|progress change (decimalBytes 7%nat) with [55]|progress change (decimalBytes 8%nat) with [56]|progress change (decimalBytes 9%nat) with [57]|progress change (decimalBytes 10%nat) with [49;48]|progress change (decimalBytes 11%nat) with [49;49]|progress change (decimalBytes 12%nat) with [49;50]|progress change (decimalBytes 13%nat) with [49;51]|progress change (decimalBytes 14%nat) with [49;52]|progress change (decimalBytes 15%nat) with [49;53]|progress change (decimalBytes 16%nat) with [49;54]|progress change (decimalBytes 17%nat) with [49;55]|progress change (decimalBytes 18%nat) with [49;56]|progress change (decimalBytes 19%nat) with [49;57]|progress change (decimalBytes 20%nat) with [50;48]|progress change (decimalBytes 21%nat) with [50;49]|progress change (decimalBytes 22%nat) with [50;50]|progress change (decimalBytes 23%nat) with [50;51]|progress change (decimalBytes 24%nat) with [50;52]|progress change (decimalBytes 25%nat) with [50;53]|progress change (decimalBytes 26%nat) with [50;54]].
Lemma two_rest opcode a b tail : two opcode ->
 rest (Protocol.Req opcode [a;b] [])++tail=List.tl (decimalBytes opcode)++32::decimalBytes a++32::decimalBytes b++10::tail.
Proof.
 unfold two. intros [->|[->|[->|[->| ->]]]];
 unfold rest,Protocol.request_bytes,Protocol.number_tokens;cbn [Protocol.opcode Protocol.arguments Protocol.object_name map Protocol.join_tokens List.tl];
 opcode_digits;cbn [List.tl List.app Protocol.join_tokens];repeat rewrite <-app_assoc;reflexivity.
Qed.
Lemma one_rest opcode value tail : one opcode ->
 rest (Protocol.Req opcode [value] [])++tail=List.tl (decimalBytes opcode)++32::decimalBytes value++10::tail.
Proof.
 unfold one. intros [->|[->|[->|[->| ->]]]];
 unfold rest,Protocol.request_bytes,Protocol.number_tokens;cbn [Protocol.opcode Protocol.arguments Protocol.object_name map Protocol.join_tokens List.tl];
 opcode_digits;cbn [List.tl List.app Protocol.join_tokens];repeat rewrite <-app_assoc;reflexivity.
Qed.
Lemma zero_rest opcode tail : zero opcode -> rest (Protocol.Req opcode [] [])++tail=List.tl (decimalBytes opcode)++10::tail.
Proof. unfold zero. intros [->| ->];unfold rest,Protocol.request_bytes,Protocol.number_tokens;
 cbn [Protocol.opcode Protocol.arguments Protocol.object_name map Protocol.join_tokens];opcode_digits;reflexivity. Qed.
Lemma named_rest opcode value name tail : named opcode ->
 rest (Protocol.Req opcode [value] name)++tail=List.tl (decimalBytes opcode)++32::decimalBytes value++32::name++10::tail.
Proof.
 unfold named. intros [->|[->| ->]];
 unfold rest,Protocol.request_bytes,Protocol.number_tokens;cbn [Protocol.opcode Protocol.arguments Protocol.object_name map Protocol.join_tokens List.tl];
 opcode_digits;cbn [List.tl List.app Protocol.join_tokens];repeat rewrite <-app_assoc;reflexivity.
Qed.
Lemma query_rest opcode name tail : query opcode ->
 rest (Protocol.Req opcode [] name)++tail=List.tl (decimalBytes opcode)++32::name++10::tail.
Proof.
 unfold query. intros [->|[->|[->|[->| ->]]]];
 unfold rest,Protocol.request_bytes,Protocol.number_tokens;cbn [Protocol.opcode Protocol.arguments Protocol.object_name map Protocol.join_tokens List.tl];
 opcode_digits;cbn [List.tl List.app Protocol.join_tokens];repeat rewrite <-app_assoc;reflexivity.
Qed.
Lemma safe_history logical : Guarantees.safe logical -> LogicalHistory.valid logical.
Proof. intros [Hhistory Hnames] index fid Hlookup. destruct (Hhistory index fid Hlookup) as [p [Hp Hproof]]. now exists p. Qed.
Lemma safe_names logical : Guarantees.safe logical -> LogicalNames.valid logical.
Proof.
 intros [Hhistory Hnames]. unfold LogicalNames.valid,Guarantees.names in *.
 eapply Forall_impl;[exact Hnames|]. intros [name meaning] Hmeaning. cbn [snd] in *.
 destruct meaning as [id flag|id|id];cbn [LogicalNames.denotes Guarantees.denotes] in *;
 first [destruct Hmeaning as [value [Hvalue Hproof]];now exists value|exact Hmeaning].
Qed.
Definition checked native logical request bs ns tail observations := exists final reply next,
 execObserved (funcdef_0__command bs ns) (native,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical request reply next /\ NativeState.represents final next /\
 NativeCommandBoundary.io native final reply tail /\ Guarantees.safe next /\ LogicalHistory.valid next /\ LogicalNames.valid next.
Lemma finish native logical request bs ns tail observations final reply next :
 Guarantees.safe logical ->
 execObserved (funcdef_0__command bs ns) (native,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])) ->
 Protocol.step logical request reply next -> NativeState.represents final next ->
 NativeCommandBoundary.io native final reply tail -> checked native logical request bs ns tail observations.
Proof.
 intros Hsafe Hrun Hstep Hstate Hio. pose proof (Guarantees.step_safe _ _ _ _ Hstep Hsafe) as HnextSafe.
 exists final,reply,next. split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hstate|].
 split;[exact Hio|]. split;[exact HnextSafe|]. split;[now apply safe_history|now apply safe_names].
Qed.

Lemma simple_io native logical final reply next tail : NativeSimpleCommands.boundary native logical final reply next tail ->
 NativeCommandBoundary.io native final reply tail.
Proof. intros (Hin & Hout & Htoken & Hprint & Herror & Hstop & Hgrowth). repeat split;assumption. Qed.
Theorem generated_canonical native logical request bs ns tail observations :
 Protocol.shape request -> supported (Protocol.opcode request) ->
 (17<length (memory native arraydef_0__meta))%nat -> (1024<=length (memory native arraydef_0__token))%nat ->
 (20<=length (memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=first (Protocol.opcode request)+1 -> meta_value native 8=0 ->
 NativeState.represents native logical -> Guarantees.safe logical -> resources native logical request ->
 stdin native=rest request++tail -> checked native logical request bs ns tail observations.
Proof.
 intros Hshape Hsupported Hmeta Htoken Hprint Hpending Herror Hstate Hsafe Hresources Hinput.
 pose proof (safe_history logical Hsafe) as HhistoryValid. pose proof (safe_names logical Hsafe) as HnamesValid.
 destruct Hresources as [HformulaRoom HclassRoom HhistoryRoom HbindingRoom HnameRoom].
 pose proof (shape_form request Hshape Hsupported) as Hform.
 destruct Hform as [opcode a b Htag|opcode value Htag|opcode Htag|opcode value name Htag|opcode name Htag].
 - destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments] in Hwords.
   inversion Hwords as [|a' values Ha Hvalues];subst a' values.
   inversion Hvalues as [|b' values Hb Hnil];subst b' values.
   rewrite (two_rest opcode a b tail Htag) in Hinput.
   unfold two in Htag. destruct Htag as [->|[->|[->|[->| ->]]]].
   + change (meta_value native 15=50) in Hpending.
     change (stdin native=32::decimalBytes a++32::decimalBytes b++10::tail) in Hinput.
     destruct (NativeSimpleCommands.generated_boundary 1 [a;b] 49 [] native logical bs ns 32 32 10 tail observations
       ltac:(unfold NativeSimpleCommands.simple_request;left;split;[tauto|eauto]) eq_refl
       Hmeta Htoken Hprint Hpending Herror HformulaRoom Hwords Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & next & Hrun & Hstep & Hnext & Hboundary).
     eapply finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|now apply simple_io in Hboundary].
   + change (meta_value native 15=51) in Hpending.
     change (stdin native=32::decimalBytes a++32::decimalBytes b++10::tail) in Hinput.
     destruct (NativeSimpleCommands.generated_boundary 2 [a;b] 50 [] native logical bs ns 32 32 10 tail observations
       ltac:(unfold NativeSimpleCommands.simple_request;left;split;[tauto|eauto]) eq_refl
       Hmeta Htoken Hprint Hpending Herror HformulaRoom Hwords Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & next & Hrun & Hstep & Hnext & Hboundary).
     eapply finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|now apply simple_io in Hboundary].
   + change (meta_value native 15=52) in Hpending.
     change (stdin native=32::decimalBytes a++32::decimalBytes b++10::tail) in Hinput.
     destruct (NativeSimpleCommands.generated_boundary 3 [a;b] 51 [] native logical bs ns 32 32 10 tail observations
       ltac:(unfold NativeSimpleCommands.simple_request;left;split;[tauto|eauto]) eq_refl
       Hmeta Htoken Hprint Hpending Herror HformulaRoom Hwords Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & next & Hrun & Hstep & Hnext & Hboundary).
     eapply finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|now apply simple_io in Hboundary].
   + change (meta_value native 15=50) in Hpending.
     change (stdin native=50::32::decimalBytes a++32::decimalBytes b++10::tail) in Hinput.
     destruct (NativeMPBoundary.generated_MP native logical bs ns a b 32 32 10 tail observations
       Hmeta Htoken Hprint Hpending Herror Ha Hb HhistoryRoom HhistoryValid Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & next & Hrun & Hstep & Hnext & HnextValid & HnextSafe & Hboundary & HformulaSame).
     eapply finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|exact (proj1 Hboundary)].
   + change (meta_value native 15=50) in Hpending.
     change (stdin native=56::32::decimalBytes a++32::decimalBytes b++10::tail) in Hinput.
     destruct (NativeMPBoundary.generated_restate native logical bs ns a b 32 32 10 tail observations
       Hmeta Htoken Hprint Hpending Herror Ha Hb HhistoryRoom HhistoryValid Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & next & Hrun & Hstep & Hnext & HnextValid & HnextSafe & Hboundary & HformulaSame).
     eapply finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|exact (proj1 Hboundary)].
 - destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments] in Hwords.
   inversion Hwords as [|value' values Hvalue Hnil];subst value' values.
   rewrite (one_rest opcode value tail Htag) in Hinput.
   unfold one in Htag. destruct Htag as [->|[->|[->|[->| ->]]]].
   + change (meta_value native 15=53) in Hpending.
     change (stdin native=32::decimalBytes value++10::tail) in Hinput.
     destruct (NativeSimpleCommands.generated_boundary 4 [value] 52 [] native logical bs ns 32 32 10 tail observations
       ltac:(unfold NativeSimpleCommands.simple_request;right;split;[reflexivity|eauto]) eq_refl
       Hmeta Htoken Hprint Hpending Herror HformulaRoom Hwords Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & next & Hrun & Hstep & Hnext & Hboundary).
     eapply finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|now apply simple_io in Hboundary].
   + change (meta_value native 15=54) in Hpending.
     change (stdin native=32::decimalBytes value++10::tail) in Hinput.
     destruct (NativeCommandBoundary.generated_set native logical bs ns value 32 10 tail observations
       Hmeta Htoken Hprint Hpending Herror HclassRoom Hvalue Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & Hrun & Hstep & Hnext & Hboundary).
     eapply finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|exact (proj1 Hboundary)].
   + change (meta_value native 15=55) in Hpending.
     change (stdin native=32::decimalBytes value++10::tail) in Hinput.
     destruct (NativeCommandBoundary.generated_abstract_total native logical bs ns value 32 10 tail observations
       Hmeta Htoken Hprint Hpending Herror HclassRoom Hvalue Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & next & Hrun & Hstep & Hnext & Hboundary).
     eapply finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|exact (proj1 Hboundary)].
   + change (meta_value native 15=50) in Hpending.
     change (stdin native=51::32::decimalBytes value++10::tail) in Hinput.
     destruct (NativeGeneralizeBoundary.generated_generalize native logical bs ns value 32 10 tail observations
       Hmeta Htoken Hprint Hpending Herror HformulaRoom HhistoryRoom Hvalue HhistoryValid Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & next & Hrun & Hstep & Hnext & HnextValid & HnextSafe & Hboundary).
     eapply finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|exact (proj1 Hboundary)].
   + change (meta_value native 15=50) in Hpending.
     change (stdin native=57::32::decimalBytes value++10::tail) in Hinput.
     destruct (NativeTheoremBoundary.generated_inspect native logical bs ns value 32 10 tail observations
       Hmeta Htoken Hprint Hpending Herror Hvalue HhistoryValid Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & Hrun & Hstep & Hnext & Hboundary).
     eapply finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|exact (proj1 Hboundary)].
 - rewrite (zero_rest opcode tail Htag) in Hinput. unfold zero in Htag. destruct Htag as [->| ->].
   + change (meta_value native 15=50) in Hpending. change (stdin native=54::10::tail) in Hinput.
     destruct (NativeCommandBoundary.generated_undo native logical bs ns 10 tail observations
       Hmeta Htoken Hprint Hpending Herror ltac:(lia) Hstate ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & Hrun & Hstep & Hnext & Hboundary).
     eapply finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|exact (proj1 Hboundary)].
   + change (meta_value native 15=50) in Hpending. change (stdin native=55::10::tail) in Hinput.
     destruct (NativeCommandBoundary.generated_reset native logical bs ns 10 tail observations
       Hmeta Htoken Hprint Hpending Herror Hstate ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & Hrun & Hstep & Hnext & Hboundary).
     eapply finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|exact (proj1 Hboundary)].
 - destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments] in Hwords.
   inversion Hwords as [|value' values Hvalue Hnil];subst value' values.
   cbn [Protocol.object_name] in HnameRoom.
   rewrite (named_rest opcode value name tail Htag) in Hinput.
   unfold named in Htag. destruct Htag as [->|[->| ->]];
     cbn [Protocol.arguments Protocol.object_name] in Hfields;destruct Hfields as [Hlength Hname].
   + change (meta_value native 15=58) in Hpending.
     change (stdin native=32::decimalBytes value++32::name++10::tail) in Hinput.
     destruct (NativeNamedBoundary.Class.generated_total_protocol native logical bs ns value name 32 32 10 tail observations
       Hmeta Htoken Hprint Hpending Herror Hvalue Hname Hstate HbindingRoom HnameRoom ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & next & Hrun & Hstep & Hnext & Hboundary & HnextSafe).
     eapply finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|exact Hboundary].
   + change (meta_value native 15=51) in Hpending.
     change (stdin native=48::32::decimalBytes value++32::name++10::tail) in Hinput.
     destruct (NativeNamedBoundary.TheoremName.generated_total_protocol native logical bs ns value name 32 32 10 tail observations
       Hmeta Htoken Hprint Hpending Herror Hvalue Hname HhistoryValid Hstate HbindingRoom HnameRoom ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & next & Hrun & Hstep & Hnext & Hboundary & HnextSafe).
     eapply finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|exact Hboundary].
   + change (meta_value native 15=51) in Hpending.
     change (stdin native=51::32::decimalBytes value++32::name++10::tail) in Hinput.
     destruct (NativeNamedBoundary.Schema.generated_total_protocol native logical bs ns value name 32 32 10 tail observations
       Hmeta Htoken Hprint Hpending Herror Hvalue Hname Hstate HbindingRoom HnameRoom ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & reply & next & Hrun & Hstep & Hnext & Hboundary & HnextSafe).
     eapply finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|exact Hboundary].
 - destruct Hshape as [Hwords Hfields]. rewrite (query_rest opcode name tail Htag) in Hinput.
   unfold query in Htag. destruct Htag as [->|[->|[->|[->| ->]]]];
     cbn [Protocol.arguments Protocol.object_name] in Hfields;destruct Hfields as [Hargs Hname].
   + change (meta_value native 15=50) in Hpending.
     change (stdin native=48::32::name++10::tail) in Hinput.
     destruct (NativeQueryCommands.Lookup.generated_total_protocol native logical bs ns name 32 10 tail observations
       Hmeta Htoken Hprint Hpending Herror Hname Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & Hrun & Hstep & Hnext & Hboundary & HnextSafe).
     eapply finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|exact Hboundary].
   + change (meta_value native 15=50) in Hpending.
     change (stdin native=53::32::name++10::tail) in Hinput.
     destruct (NativeQueryCommands.Query.generated_total_protocol CommandNameQueryExecution.Setness native logical bs ns name 32 10 tail observations
       Hmeta Htoken Hprint Hpending Herror Hname Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & Hrun & Hstep & Hnext & Hboundary & HnextSafe).
     eapply finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|exact Hboundary].
   + change (meta_value native 15=51) in Hpending.
     change (stdin native=49::32::name++10::tail) in Hinput.
     destruct (NativeQueryCommands.Recall.generated_total_protocol native logical bs ns name 32 10 tail observations
       Hmeta Htoken Hprint Hpending Herror HhistoryRoom HnamesValid HhistoryValid Hname Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & Hrun & Hstep & Hnext & Hboundary & HnextSafe).
     eapply finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|exact Hboundary].
   + change (meta_value native 15=51) in Hpending.
     change (stdin native=53::32::name++10::tail) in Hinput.
     destruct (NativeQueryCommands.Query.generated_total_protocol CommandNameQueryExecution.Kind native logical bs ns name 32 10 tail observations
       Hmeta Htoken Hprint Hpending Herror Hname Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & Hrun & Hstep & Hnext & Hboundary & HnextSafe).
     eapply finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|exact Hboundary].
   + change (meta_value native 15=51) in Hpending.
     change (stdin native=54::32::name++10::tail) in Hinput.
     destruct (NativeQueryCommands.Arity.generated_total_protocol native logical bs ns name 32 10 tail observations
       Hmeta Htoken Hprint Hpending Herror HnamesValid Hname Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput)
     as (final & Hrun & Hstep & Hnext & Hboundary & HnextSafe).
     eapply finish;[exact Hsafe|exact Hrun|exact Hstep|exact Hnext|exact Hboundary].
Qed.
Lemma resources_names before after logical request :
 memory after arraydef_0__names=memory before arraydef_0__names ->
 resources before logical request -> resources after logical request.
Proof.
 intros Hnames [Hform Hclass Hhistory Hbindings Hname]. constructor;try assumption. now rewrite Hnames.
Qed.
(** Entry form consumed directly by the actual tapeEnd command loop. It derives
    the pending state and every parser premise from canonical request bytes. *)
Theorem generated_tape_step native logical request bs ns tail observations :
 Protocol.shape request -> supported (Protocol.opcode request) ->
 (17<length (memory native arraydef_0__meta))%nat -> (1024<=length (memory native arraydef_0__token))%nat ->
 (20<=length (memory native arraydef_0__printBuffer))%nat -> meta_value native 8=0 ->
 NativeState.represents native logical -> Guarantees.safe logical -> resources native logical request ->
 stdin native=Protocol.request_bytes request++tail ->
 exists ch unread,
 0<=ch<256 /\ stdin native=ch::unread /\
 checked (CommandLoopExecution.pending_state (withInput native unread) ch) logical request bs ns tail observations.
Proof.
 intros Hshape Hsupported Hmeta Htoken Hprint Herror Hstate Hsafe Hresources Hinput.
 destruct (request_encoding request Hsupported) as [Hwire Hbyte].
 exists (first (Protocol.opcode request)),(rest request++tail). split;[exact Hbyte|]. split.
 - rewrite Hinput,Hwire;reflexivity.
 - set (pending:=CommandLoopExecution.pending_state (withInput native (rest request++tail)) (first (Protocol.opcode request))).
   assert (HpendingMeta:(17<length (memory pending arraydef_0__meta))%nat).
   { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_length. exact Hmeta. }
   assert (HpendingToken:(1024<=length (memory pending arraydef_0__token))%nat).
   { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact Htoken. }
   assert (HpendingPrint:(20<=length (memory pending arraydef_0__printBuffer))%nat).
   { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact Hprint. }
   assert (HpendingValue:meta_value pending 15=first (Protocol.opcode request)+1).
   { unfold pending,CommandLoopExecution.pending_state. apply meta_store_same. change (15<length (memory native arraydef_0__meta))%nat;lia. }
   assert (HpendingError:meta_value pending 8=0).
   { unfold pending,CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact Herror. }
   assert (HpendingState:NativeState.represents pending logical).
   { unfold pending,CommandLoopExecution.pending_state. apply NativeSession.state_meta;try lia. now apply NativeSession.state_input. }
   assert (HpendingResources:resources pending logical request).
   { eapply resources_names;[|exact Hresources]. unfold pending,CommandLoopExecution.pending_state. now rewrite store_meta_other by discriminate. }
   exact (generated_canonical pending logical request bs ns tail observations Hshape Hsupported
     HpendingMeta HpendingToken HpendingPrint HpendingValue HpendingError HpendingState Hsafe HpendingResources eq_refl).
Qed.
End NativeBasicDispatcher.
