Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Leapfrog.FinType.

Set Universe Polymorphism.
Section TypeNeq.
  Context (A B: Type).
  Context `{Finite A}.
  Context `{Finite B}.
  Lemma card_eq_raw:
    A = B ->
    forall (xs: list A) (ys: list B),
      (forall x, In x xs) ->
      (forall y, In y ys) ->
      NoDup xs ->
      NoDup ys ->
      length xs = length ys.
  Proof.
    intro eq.
    subst B.
    intros.
    eapply Nat.le_antisymm;
      eapply NoDup_incl_length;
      unfold incl;
      eauto.
  Qed.

  Lemma card_neq:
    card A <> card B ->
    A <> B.
  Proof.
    unfold "<>".
    unfold card.
    destruct H0, H2.
    eauto using card_eq_raw.
  Qed.

End TypeNeq.

