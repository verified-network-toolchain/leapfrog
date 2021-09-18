Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Import List.ListNotations.

Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.Relations.
Require Import Poulet4.P4automata.Bisimulations.WPLeaps.
Require Import Poulet4.P4automata.Bisimulations.AlgorithmicProofs.

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
  Instance H'_eq_dec: EquivDec.EqDec (P4A.H' H) eq := P4A.H'_eq_dec (H_eq_dec:=H_eq_dec).
  Context `{H_finite: @Finite (Syntax.H' H) _ H'_eq_dec}.

  Variable (a: P4A.t S H).

  Variable (wp: P4A.t S H ->
                conf_rel S H ->
                list (conf_rel S H)).

  Notation conf := (configuration (P4A.interp a)).

  Variable (top: rel conf).
  Variable (top_closed: forall x y b, top x y -> top (step x b) (step y b)).

  Notation "⟦ x ⟧" := (interp_crel a top x).
  Notation "⦇ x ⦈" := (interp_conf_rel a x).
  Notation "R ⊨ q1 q2" := (⟦R⟧ q1 q2) (at level 40).
  Notation "R ⊨ S" := (interp_entailment a top {| e_prem := R; e_concl := S |}) (at level 40).
  Notation δ := step.

  Lemma ctopbbd_topbdd:
    forall R,
      ctopbdd a top R ->
      topbdd a top ⟦R⟧.
  Proof.
    unfold ctopbdd, topbdd.
    induction R; simpl; intros.
    - assumption.
    - inversion H1.
      eauto.
  Qed.

  Lemma ctopbdd_app:
    forall C T,
      ctopbdd a top C ->
      ctopbdd a top T ->
      ctopbdd a top (C ++ T).
  Proof.
    unfold ctopbdd.
    intros.
    rewrite in_app_iff in *.
    intuition.
  Qed.

  Lemma topbdd_mono:
    forall (R S: rel conf),
      (forall x y, R x y -> S x y) ->
      topbdd a top S ->
      topbdd a top R.
  Proof.
    unfold topbdd.
    auto.
  Qed.

  Lemma syn_pre_implies_sem_pre:
    forall R S q1 q2,
      pre_bisimulation a wp top R S q1 q2 ->
      ctopbdd a top R ->
      ctopbdd a top S ->
      safe_wp_1bit a wp top ->
      wp_bdd a wp top ->
      Algorithmic.pre_bisimulation (P4A.interp a)
                              top
                              (map (interp_conf_rel a) R)
                              (map (interp_conf_rel a) S)
                              q1 q2.
  Proof.
    intros R S q1 q2 Hstep.
    induction Hstep.
    - simpl.
      constructor.
      eauto.
    - simpl.
      intros.
      econstructor 2; eauto.
      eapply IHHstep; eauto.
      unfold ctopbdd; intros.
      eauto with datatypes.
    - rewrite map_app in IHHstep.
      subst.
      intros.
      econstructor 3; eauto.
      eapply IHHstep; eauto.
      + unfold ctopbdd in *.
        intros.
        simpl (In _ _) in *.
        intuition.
      + eapply ctopbdd_app.
        * eapply H5.
          eapply H3.
          eauto with datatypes.
        * unfold ctopbdd in *; simpl (In _ _ ) in *; eauto.
      + intros.
        eapply H4; eauto.
        eapply AlgorithmicProofs.interp_rels_top; eauto.
  Qed.

End WPLeapsProofs.
