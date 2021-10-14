Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Import List.ListNotations.

Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.Relations.
Require Import Poulet4.P4automata.Bisimulations.Leaps.
Require Import Poulet4.P4automata.Bisimulations.WPLeaps.
Require Import Poulet4.P4automata.Bisimulations.AlgorithmicProofs.
Require Import Poulet4.P4automata.Reachability.

Section WPLeapsProofs.

  (* State identifiers. *)
  Variable (S1: Type).
  Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
  Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

  Variable (S2: Type).
  Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
  Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

  Notation S := ((S1 + S2)%type).

  (* Header identifiers. *)
  Variable (H: nat -> Type).
  Context `{H_eq_dec: forall n, EquivDec.EqDec (H n) eq}.
  Context `{H'_eq_dec: EquivDec.EqDec (P4A.H' H) eq}.
  Context `{H_finite: @Finite (Syntax.H' H) _ H'_eq_dec}.

  Variable (a: P4A.t S H).

  Variable (wp: conf_rel a ->
                list (conf_rel a)).

  Notation conf := (configuration (P4A.interp a)).

  Variable (top: rel conf).
  Variable (top_closed: forall x y b, top x y -> top (step x b) (step y b)).

  Notation "⟦ x ⟧" := (interp_crel a top x).
  Notation "⦇ x ⦈" := (interp_conf_rel a x).
  Notation "R ⊨ q1 q2" := (⟦R⟧ q1 q2) (at level 40).
  Notation "R ⊨ S" := (interp_entailment a top {| e_prem := R; e_concl := S |}) (at level 40).
  Notation δ := step.

  Notation "ctx , ⟨ s1 , n1 ⟩ ⟨ s2 , n2 ⟩ ⊢ b" :=
    ({| cr_st :=
          {| cs_st1 := {| st_state := s1; st_buf_len := n1 |};
             cs_st2 := {| st_state := s2; st_buf_len := n2 |}; |};
        cr_ctx := ctx;
        cr_rel := b|}) (at level 10).
  Notation btrue := (BRTrue _ _).
  Notation bfalse := (BRFalse _ _).

  Lemma interp_crel_app:
    forall R1 R2 q1 q2,
      interp_crel a top (R1 ++ R2) q1 q2 <->
      interp_crel a top R1 q1 q2 /\
      interp_crel a top R2 q1 q2.
  Proof.
  Admitted.

  Lemma pre_bisimulation_implies_interp_crel:
    forall R T S q1 q2,
      pre_bisimulation a wp top R T S ->
      interp_conf_rel' S q1 q2 ->
      top q1 q2 ->
      interp_crel a top (T ++ R) q1 q2.
  Proof.
    intros.
    induction H0.
    - rewrite app_nil_l.
      apply H0; simpl; auto.
    - destruct H0; [|contradiction].
      specialize (IHpre_bisimulation H1).
      repeat rewrite interp_crel_app in *.
      rewrite interp_crel_cons in *.
      intuition.
    - destruct H0; [contradiction|].
      specialize (IHpre_bisimulation H1).
      repeat rewrite interp_crel_app in *.
      rewrite interp_crel_cons in *.
      intuition.
  Qed.

  Lemma pre_bisimulation_implies_equally_accepting:
    forall S q1 q2 s1 s2,
      pre_bisimulation a wp top []
        (mk_init _ _ _ _ (length (valid_state_pairs a)) s1 s2) S ->
      interp_conf_rel' S q1 q2 ->
      top q1 q2 ->
      (accepting q1 <-> accepting q2).
  Proof.
  Admitted.

  Lemma wp_leaps_implies_bisim_leaps:
    forall S q1 q2 s1 s2,
      pre_bisimulation a wp top []
        (mk_init _ _ _ _ (length (valid_state_pairs a)) s1 s2) S ->
      interp_conf_rel' S q1 q2 ->
      top q1 q2 ->
      bisimilar_with_leaps (P4A.interp a) q1 q2.
  Proof.
    intros; cofix C; constructor.
    - eapply pre_bisimulation_implies_equally_accepting;
      [exact H0 | auto | auto].
    - (* Guarded. *)
  Abort.

End WPLeapsProofs.
