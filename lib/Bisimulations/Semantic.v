Require Import Coq.Lists.List.

Require Import Leapfrog.P4automaton.
Require Import Leapfrog.FinType.
Require Import Leapfrog.Relations.

Section Semantic.
  Context {a1 a2: p4automaton}.
  Notation rel := (configuration a1 -> configuration a2 -> Prop).

  (* A relation is a bisimulation if (1) related states are equally accepting
     and (2) related states transition to related states. *)
  Definition bisimulation (R: rel) :=
    forall q1 q2,
      R q1 q2 ->
      (accepting q1 <-> accepting q2) /\
      forall b, R (step q1 b) (step q2 b).

  (* Two states are bisimilar if a bisimulation relates them. Note that this
     is, by construction, the largest possible bisimulation. *)
  Definition bisimilar q1 q2 :=
    exists R, bisimulation R /\ R q1 q2.

  (* Bisimilar states are language equivalent. *)
  Lemma bisimilar_implies_equiv :
    forall (c1: configuration a1) (c2: configuration a2),
      bisimilar c1 c2 ->
      lang_equiv c1 c2.
  Proof.
    intros.
    unfold lang_equiv.
    intros; revert c1 c2 H.
    induction input; intros.
    - unfold accepted.
      simpl.
      unfold bisimilar in H.
      destruct H as [R [? ?]].
      now apply H in H0.
    - unfold accepted.
      autorewrite with follow.
      apply IHinput.
      unfold bisimilar in H.
      destruct H as [R [? ?]].
      exists R.
      apply H in H0.
      easy.
  Qed.

  (* Language equivalence is a bisimulation relation. *)
  Lemma lang_equiv_is_bisimulation :
      bisimulation lang_equiv
  .
  Proof.
    unfold bisimulation; intros.
    split.
    - apply (H nil).
    - intros.
      unfold lang_equiv in *.
      intros.
      specialize (H (b :: input)).
      apply H.
  Qed.

  (* The last lemma tells us that language equivalence implies bisimilarity. *)
  Lemma equiv_implies_bisimilar:
    forall (c1: configuration a1) (c2: configuration a2),
      lang_equiv c1 c2 -> bisimilar c1 c2.
  Proof.
    intros.
    exists lang_equiv.
    split; try easy.
    apply lang_equiv_is_bisimulation.
  Qed.

  (* Bisimilarity is sound and complete for language equivalence. *)
  Theorem bisimilar_iff_lang_equiv:
    forall (c1: configuration a1) (c2: configuration a2),
      lang_equiv c1 c2 <-> bisimilar c1 c2.
  Proof.
    split.
    - apply equiv_implies_bisimilar.
    - apply bisimilar_implies_equiv.
  Qed.

End Semantic.
