Require Import Coq.Lists.List.
Import ListNotations.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.Sum.
Require Import Leapfrog.SumProofs.
Require Import Leapfrog.WP.
Require Import Leapfrog.P4automaton.
Require Import Leapfrog.Bisimulations.Semantic.
Require Import Leapfrog.Bisimulations.Leaps.
Require Import Leapfrog.Bisimulations.LeapsProofs.
Require Import Leapfrog.Bisimulations.WPLeaps.
Require Import Leapfrog.Bisimulations.WPLeapsProofs.

Notation "ctx , ⟨ s1 , n1 ⟩ ⟨ s2 , n2 ⟩ ⊢ b" :=
  ({| cr_st :=
        {| cs_st1 := {| st_state := s1; st_buf_len := n1 |};
           cs_st2 := {| st_state := s2; st_buf_len := n2 |}; |};
      cr_ctx := ctx;
      cr_rel := b|}) (at level 10).
Notation btrue := (BRTrue _ _).
Notation bfalse := (BRFalse _ _).
Notation "a ⇒ b" := (BRImpl a b) (at level 40).

Section LangEquivToPreBisim.
  Set Implicit Arguments.

  (* State identifiers. *)
  Variable (St1: Type).
  Context `{St1_eq_dec: EquivDec.EqDec St1 eq}.
  Context `{St1_finite: @FinType.Finite St1 _ St1_eq_dec}.

  Variable (St2: Type).
  Context `{St2_eq_dec: EquivDec.EqDec St2 eq}.
  Context `{St2_finite: @FinType.Finite St2 _ St2_eq_dec}.

  (* Header identifiers. *)
  Variable (Hdr1: Type).
  Variable (Hdr1_sz : Hdr1 -> nat).
  Context `{Hdr1_eq_dec: EquivDec.EqDec Hdr1 eq}.
  Context `{Hdr1_finite: @FinType.Finite Hdr1 _ Hdr1_eq_dec}.

  Variable (Hdr2: Type).
  Variable (Hdr2_sz : Hdr2 -> nat).
  Context `{Hdr2_eq_dec: EquivDec.EqDec Hdr2 eq}.
  Context `{Hdr2_finite: @FinType.Finite Hdr2 _ Hdr2_eq_dec}.

  Variable (a1: Syntax.t St1 Hdr1_sz).
  Variable (a2: Syntax.t St2 Hdr2_sz).

  Notation St := (St1 + St2)%type.

  (* To prove language equivalence, it is sufficient to establish a certain
     pre-bisimulation, as it will give you a bisimulation with leaps and
     hence a bisimulation, which implies language equivalence. *)
  Lemma lang_equiv_to_pre_bisim:
    forall (s1: St1) (s2: St2),
      let init := mk_init _ _ _ _ (Sum.sum a1 a2) s1 s2 in

      (forall q1 q2,
          interp_conf_rel' (BCEmp, ⟨ inl (inl s1), 0 ⟩ ⟨ inl (inr s2), 0⟩ ⊢ btrue) q1 q2 ->
          pre_bisimulation (Sum.sum a1 a2)
                           (Reachability.reachable_states (Sum.sum a1 a2) s1 s2)
                           (wp (a:=Sum.sum a1 a2))
                           []
                           init
                           q1
                           q2) ->
      lang_equiv_state (P4A.interp a1) (P4A.interp a2) s1 s2.
  Proof.
    intros.
    eapply SumProofs.sum_thing; [typeclasses eauto | typeclasses eauto |].
    unfold lang_equiv_state.
    intros.
    match goal with
    | |- lang_equiv ?c1t ?c2t =>
        set (cr0 := {| cr_st :=
                      {| cs_st1 := conf_to_state_template (a:=Sum.sum a1 a2) c1t;
                        cs_st2 := conf_to_state_template (a:=Sum.sum a1 a2) c2t; |};
                      cr_ctx := BCEmp;
                      cr_rel := btrue; |});
        unfold conf_to_state_template in cr0; simpl in cr0;
        set (c1 := c1t);
        set (c2 := c2t)
    end.
    assert (interp_conf_rel' cr0 c1 c2).
    {
      unfold interp_conf_rel'.
      cbv; intuition.
      autorewrite with interp_store_rel.
      tauto.
    }
    generalize dependent c1.
    generalize dependent c2.
    subst cr0.
    intros.
    apply bisimilar_implies_equiv.
    apply bisimilar_iff_bisimilar_with_leaps.
    eapply wp_leaps_implies_bisim_leaps with (s1 := s1) (s2 := s2).
    2:{
      unfold WPLeapsProofs.top.
      unfold Reachability.reachable_states.
      unfold Reachability.build_state_pairs, Reachability.build_state_pair.
      remember (length (Reachability.valid_state_pairs (Sum.sum a1 a2))) as fuel.
      clear Heqfuel.
      induction fuel.
      - cbv.
        destruct c1, c2.
        destruct H0 as [[Hc1 Hc2] _].
        repeat match goal with
               | H: interp_state_template _ _ |- _ =>
                   apply Reachability.interp_state_template_definite in H;
                   cbv in H;
                   inversion H
               end.
        tauto.
      - simpl.
        unfold Reachability.reachable_step.
        apply List.nodup_In.
        apply List.in_or_app.
        right.
        apply IHfuel.
    }
    auto.
  Qed.
End LangEquivToPreBisim.
