Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.PreBisimulationSyntax.

Ltac prep_equiv :=
  unfold Equivalence.equiv, RelationClasses.complement in *;
  program_simpl; try congruence.

Obligation Tactic := prep_equiv.

Module IncrementalBits.
  Inductive state :=
  | Start
  | Finish.
  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [Start; Finish] |}.
  Next Obligation.
    repeat constructor;
      repeat match goal with
             | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
             | |- ~ List.In _ [] => apply List.in_nil
             | |- ~ List.In _ (_ :: _) => unfold not; intros
             | H: List.In _ (_::_) |- _ => inversion H; clear H
             | _ => discriminate
             end.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Inductive header :=
  | Pref
  | Suf.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Program Instance header_finite: @Finite header _ header_eq_dec :=
    {| enum := [Pref; Suf] |}.
  Next Obligation.
    repeat constructor;
      repeat match goal with
             | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
             | |- ~ List.In _ [] => apply List.in_nil
             | |- ~ List.In _ (_ :: _) => unfold not; intros
             | H: List.In _ (_::_) |- _ => inversion H; clear H
             | _ => discriminate
             end.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Definition states (s: state) :=
    match s with
    | Start =>
      {| st_op := OpExtract 1 (HRVar Pref);
         st_trans := P4A.TSel (CExpr (EHdr (HRVar Pref)))
                              [{| sc_pat := PExact (VBits [true]);
                                  sc_st := inl Finish |}]
                              (inr false) |}
    | Finish =>
      {| st_op := OpExtract 1 (HRVar Suf);
         st_trans := P4A.TGoto _ (inr true) |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End IncrementalBits.

Module BigBits.
  Inductive state :=
  | Parse.
  Global Instance state_eqdec: EquivDec.EqDec state eq.
  vm_compute.
  intros.
  left.
  destruct x; destruct x0; trivial.
  Defined.
  Global Program Instance state_finite: @Finite state _ state_eqdec :=
    {| enum := [Parse] |}.
  Next Obligation.
    repeat constructor;
      repeat match goal with
             | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
             | |- ~ List.In _ [] => apply List.in_nil
             | |- ~ List.In _ (_ :: _) => unfold not; intros
             | H: List.In _ (_::_) |- _ => inversion H; clear H
             | _ => discriminate
             end.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Inductive header :=
  | Pref
  | Suf.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Program Instance header_finite: @Finite header _ header_eq_dec :=
    {| enum := [Pref; Suf] |}.
  Next Obligation.
    repeat constructor;
      repeat match goal with
             | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
             | |- ~ List.In _ [] => apply List.in_nil
             | |- ~ List.In _ (_ :: _) => unfold not; intros
             | H: List.In _ (_::_) |- _ => inversion H; clear H
             | _ => discriminate
             end.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Definition states (s: state) :=
    match s with
    | Parse =>
      {| st_op := OpSeq
        (OpExtract 1 (HRVar Pref))
        (OpExtract 1 (HRVar Suf));
         st_trans := P4A.TSel (CExpr (EHdr (HRVar Pref)))
                              [{| sc_pat := PExact (VBits [true]);
                                  sc_st := inr true |}]
                              (inr (A := state) false) |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End BigBits.

Module OneBit.
  Inductive state :=
  | Parse.
  Global Instance state_eqdec: EquivDec.EqDec state eq.
  vm_compute.
  intros.
  left.
  destruct x; destruct x0; trivial.
  Defined.
  Global Program Instance state_finite: @Finite state _ state_eqdec :=
    {| enum := [Parse] |}.
  Next Obligation.
    repeat constructor;
      repeat match goal with
             | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
             | |- ~ List.In _ [] => apply List.in_nil
             | |- ~ List.In _ (_ :: _) => unfold not; intros
             | H: List.In _ (_::_) |- _ => inversion H; clear H
             | _ => discriminate
             end.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Inductive header :=
  | Pref.

  Global Instance hdr_eqdec: EquivDec.EqDec header eq.
  vm_compute.
  intros.
  left.
  destruct x; destruct x0; trivial.
  Defined.
  Global Program Instance header_finite: @Finite header _ hdr_eqdec :=
    {| enum := [Pref] |}.
  Next Obligation.
    repeat constructor;
      repeat match goal with
             | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
             | |- ~ List.In _ [] => apply List.in_nil
             | |- ~ List.In _ (_ :: _) => unfold not; intros
             | H: List.In _ (_::_) |- _ => inversion H; clear H
             | _ => discriminate
             end.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Definition states (s: state) :=
    match s with
    | Parse =>
      {| st_op := (OpExtract 2 (HRVar Pref));
         st_trans := P4A.TSel (CExpr (ESlice (EHdr (HRVar Pref)) 1 0))
                              [{| sc_pat := PExact (VBits [true]);
                                  sc_st := inr true |}]
                              (inr (A := state) false) |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End OneBit.

Module IncrementalSeparate.

  Definition state: Type := Sum.S IncrementalBits.state BigBits.state.
  Global Instance state_eq_dec: EquivDec.EqDec state eq :=
    ltac:(typeclasses eauto).

  Definition header := Sum.H IncrementalBits.header BigBits.header.
  Global Instance header_eq_dec: EquivDec.EqDec header eq :=
    ltac:(typeclasses eauto).
  Global Instance header_finite: @Finite header _ header_eq_dec :=
    ltac:(typeclasses eauto).

  Definition aut := Sum.sum IncrementalBits.aut BigBits.aut.
End IncrementalSeparate.

Module SeparateCombined.
  Definition state: Type := Sum.S BigBits.state OneBit.state.
  Global Instance state_eq_dec: EquivDec.EqDec state eq :=
    ltac:(typeclasses eauto).

  Definition header := Sum.H BigBits.header OneBit.header.
  Global Instance header_eq_dec: EquivDec.EqDec header eq :=
    ltac:(typeclasses eauto).
  Global Instance header_finite: @Finite header _ header_eq_dec :=
    ltac:(typeclasses eauto).

  Definition aut := Sum.sum BigBits.aut OneBit.aut.
End SeparateCombined.

Module IncrementalCombined.
  Definition state: Type := Sum.S IncrementalBits.state OneBit.state.
  Global Instance state_eq_dec: EquivDec.EqDec state eq :=
    ltac:(typeclasses eauto).

  Definition header := Sum.H IncrementalBits.header OneBit.header.
  Global Instance header_eq_dec: EquivDec.EqDec header eq :=
    ltac:(typeclasses eauto).
  Global Instance header_finite: @Finite header _ header_eq_dec :=
    ltac:(typeclasses eauto).

  Definition aut := Sum.sum IncrementalBits.aut OneBit.aut.
End IncrementalCombined.


Require Import Poulet4.P4automata.Examples.ProofHeader.
(* Require Import Poulet4.P4automata.Examples.SimpleSplitProofSmallInitLeap. *)
From Hammer Require Import Tactics.


Notation i := (separated _ _ _ IncrementalSeparate.aut).
Notation "⟦ x ⟧" := (interp_crel i x).
Notation "⦇ x ⦈" := (interp_conf_rel (a:=IncrementalSeparate.aut) x).
Notation "R ⊨ q1 q2" := (⟦R⟧ q1 q2) (at level 40).
Notation "R ⊨ S" := (forall q1 q2, ⟦R⟧ q1 q2 -> ⦇S⦈ q1 q2) (at level 40).

Lemma forall_exists:
  forall {A B} (P: A -> B -> Prop),
  (exists x y, ~ P x y) ->
  ~ (forall x y, P x y).
Proof.
  firstorder.
Qed.

Lemma double_neg: 
  forall {A B} (P: A -> B -> Prop),
  (exists x y, P x y) ->
  (exists x y, ~ (P x y -> False)).
Proof.
  intros.
  destruct H as [x [y H]].
  exists x.
  exists y.
  intuition.
Qed.

Lemma split_univ:
  forall (A B : Type) (P : A * B -> Prop),
    (forall (x : A) (y : B), P (x, y)) <-> (forall x : A * B, P x).
Proof.
  firstorder.
  destruct x.
  firstorder.
Qed.

(* Ltac break_products :=
  match goal with 
  | *)

Lemma exists_unused:
  forall A,
    inhabited A ->  
    forall P: Prop,
    exists (_: A), P <-> P.
Proof.
  intros.
  inversion H.
  firstorder.
Qed.
Lemma flip_ex_impl:
  forall A B (P Q: A -> B -> Prop),
    (exists x y, P x y /\ ~ Q x y) ->
    (exists x y, ~ (P x y -> Q x y)).
Proof.
  firstorder.
Qed.

Definition states_match {S H} {S_eq_dec: EquivDec.EqDec S eq} (c1 c2: conf_rel S H) : bool :=
  if conf_state_eq_dec c1.(cr_st) c2.(cr_st)
  then true
  else false.

Lemma filter_entails:
  forall R C,
    R ⊨ C <-> List.filter (states_match C) R ⊨ C.
Proof.
Admitted.

Lemma no_state:
  forall R S,
    (forall q1 q2 (_ : interp_crel (separated _ _ _ IncrementalSeparate.aut) R q1 q2),
        interp_conf_rel S q1 q2)
    <->
    (forall st1 (buf1: n_tuple bool S.(cr_st).(cs_st1).(st_buf_len)) st2 (buf2: n_tuple bool S.(cr_st).(cs_st2).(st_buf_len)),
        let q1 := (S.(cr_st).(cs_st1).(st_state), st1, t2l _ _ buf1) in
        let q2 := (S.(cr_st).(cs_st2).(st_state), st2, t2l _ _ buf2) in
        interp_crel (separated _ _ _ IncrementalSeparate.aut) R q1 q2 ->
        forall valu : bval (cr_ctx S), interp_store_rel (cr_rel S) valu q1 q2).
Proof.
  intros.
  unfold "⊨".
  split; intros.
  - unfold interp_conf_rel in *.
    simpl.
    intros.
Admitted.

Ltac disprove_sat :=
  rewrite filter_entails;
  simpl;
  rewrite no_state;
  repeat (unfold interp_conf_rel, interp_conf_state, interp_state_template, interp_store_rel || cbn);
  eapply forall_exists;
  repeat (setoid_rewrite <- split_univ; cbn);
  repeat (setoid_rewrite <- split_ex; cbn);
  solve [sauto].

Ltac disprove_sat_old :=
  unfold interp_conf_rel;
  simpl;
  eapply forall_exists;
  apply flip_ex_impl;
  unfold "⊨";
  simpl;
  repeat setoid_rewrite <- split_ex;
  simpl;
  unfold interp_conf_state, interp_state_template;
  simpl;
  unfold i;
  repeat (simpl (fst _) || simpl (snd _));
  unfold Sum.H, P4A.store, P4A.Env.t;
  unfold not;
  sauto.

Ltac extend_bisim a wp R C :=
      let H := fresh "H" in
      assert (H: ~(R ⊨ C)) by disprove_sat;
        pose (t := wp a C);
        eapply PreBisimulationExtend with (H0 := right H) (W := t);
        [ tauto | reflexivity |];
        compute in t;
        simpl (_ ++ _);
        unfold t;
        clear t; 
        clear H.

Ltac extend_bisim_old a wp R C :=
      let H := fresh "H" in
      assert (H: ~(R ⊨ C)) by disprove_sat_old;
        pose (t := wp a C);
        eapply PreBisimulationExtend with (H0 := right H) (W := t);
        [ tauto | reflexivity |];
        compute in t;
        simpl (_ ++ _);
        unfold t;
        clear t; 
        clear H.

Ltac prove_sat :=
  unfold interp_conf_rel;
  unfold "⊨";
  unfold interp_conf_state, interp_state_template;
  simpl;
  sauto limit:5000.

Ltac skip_bisim a wp R C :=
  let H := fresh "H" in
  assert (H: R ⊨ C)
    by prove_sat;
  eapply PreBisimulationSkip with (H0:=left H);
  [ exact I | ];
  clear H.

Ltac solve_bisim :=
  match goal with
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    extend_bisim a wp R C
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    skip_bisim a wp R C
  | |- pre_bisimulation _ _ _ _ [] _ _ =>
    apply PreBisimulationClose
  end.

Ltac find v :=
  match goal with
  | v := ?value : _ |- _ => value
  end.

Ltac build_store hdrs P store :=
  idtac hdrs;
  idtac P;
  idtac store;
  match hdrs with
  | nil => constr:(P store)
  | ?h :: ?hdrs' =>
    let x := fresh "h" in
    let old_store := find store in
    clear store;
    set (store := (h, x) :: old_store);
    build_store hdrs' constr:(exists y, P store) store
  end.

Ltac simp_exists_store :=
  match goal with
  | |- exists (x: P4A.store ?H), @?P x =>
    pose (hdrs := enum H);
    cbv in hdrs;
    let store := fresh "store" in
    set (store := []: P4A.store H);
    cut (ltac:(build_store ltac:(find hdrs) P store))
  end.

Lemma prebisim_incremental_sep:
  pre_bisimulation IncrementalSeparate.aut
                   (WPSymLeap.wp (H:=IncrementalSeparate.header))
                   (separated _ _ _ IncrementalSeparate.aut)
                   nil
                   (mk_init 10 IncrementalSeparate.aut IncrementalBits.Start BigBits.Parse)
                   (inl (inl IncrementalBits.Start), [], [])
                   (inl (inr BigBits.Parse), [], []).
Proof.
  set (r := (mk_init 10 IncrementalSeparate.aut IncrementalBits.Start BigBits.Parse)).
  cbv in r.
  subst r.
  solve_bisim.
  match goal with
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    assert (H: ~(R ⊨ C))
  end.
  {
      rewrite filter_entails.
      simpl.
      rewrite no_state.
      repeat (unfold interp_conf_rel, interp_conf_state, interp_state_template, interp_store_rel || cbn).
      eapply forall_exists.
      repeat (setoid_rewrite <- split_univ; cbn).
      repeat (setoid_rewrite <- split_ex; cbn).
      unfold not.
      pose proof (ltac:(simp_exists_store)).

      match goal with
      | |- exists (x: P4A.store ?H), @?P x =>
        let hdrs := fresh "hdrs" in
        set (hdrs := enum H);
          cbv in hdrs;
          match goal with
          | hdrs := ?h : _ |- _ => idtac h
          end
      end.
      
      
                  
        match hdrs with
        | ?h :: _ => idtac h
        end
      end.
      
      
          build_store hdrs P (@nil (H * list bool))
      end.
      simp_exists_store.

{
  intros.
  destruct H as [x0 [x1 [x2 [x3 ?]]]].
  exists ([(inl IncrementalBits.Pref, P4A.VBits x0);
      (inl IncrementalBits.Suf, P4A.VBits x1);
      (inr BigBits.Pref, P4A.VBits x2); (inr BigBits.Suf, P4A.VBits x3)]).
  eauto.
}

      match goal with
      | |- exists (x: P4A.store ?H), @?P x =>
        cut (exists y0 y1 y2 y3,
                   P ([(inl IncrementalBits.Pref, P4A.VBits y0);
                       (inl IncrementalBits.Suf, P4A.VBits y1);
                       (inr BigBits.Pref, P4A.VBits y2);
                       (inr BigBits.Suf, P4A.VBits y3)]))
      end.
      {
        intros.
        destruct H as [x0 [x1 [x2 [x3 ?]]]].
        exists ([(inl IncrementalBits.Pref, P4A.VBits x0);
            (inl IncrementalBits.Suf, P4A.VBits x1);
            (inr BigBits.Pref, P4A.VBits x2); (inr BigBits.Suf, P4A.VBits x3)]).
        eauto.
      }
      repeat eexists.
      sauto.
  }
    );
    pose (t := wp a C);
        eapply PreBisimulationExtend with (H0 := right H) (W := t);
        [ tauto | reflexivity |];
        compute in t;
        simpl (_ ++ _);
        unfold t;
        clear t; 
        clear H
  end.
  
  solve_bisim.
  solve_bisim.
  solve_bisim.
  solve_bisim.
  solve_bisim.
  solve_bisim.
  solve_bisim.
  solve_bisim.

  solve_bisim.
  solve_bisim.
  solve_bisim.
  solve_bisim.



  solve_bisim.
  solve_bisim.
  solve_bisim.

  repeat (unfold interp_conf_rel, interp_conf_state, interp_state_template || cbn).
  intuition eauto;
  firstorder (try congruence);
  sauto limit:5000.
Time Qed.
