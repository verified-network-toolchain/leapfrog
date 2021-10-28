Require Import Coq.Lists.List.

Require Import Poulet4.FinType.
Require Import Poulet4.TypeNeq.
Require Import Poulet4.P4automata.Ntuple.

Definition next_tuple (n: nat) (t: n_tuple bool n) : n_tuple bool n.
  revert t.
  induction n; simpl; intros t; destruct t.
  - exact tt.
  - destruct b eqn:?.
    + exact (IHn n0, false).
    + exact (n0, true).
Defined.

Fixpoint enum_tuples' {n: nat} k (t: n_tuple bool n) :=
  match k with
  | 0 => nil
  | S k => t :: enum_tuples' k (next_tuple n t)
  end.

Definition enum_tuples (n: nat) : list (n_tuple bool n) :=
  enum_tuples' (Nat.pow 2 n) (n_tuple_repeat n false).

Lemma length_enum_tuples':
  forall {n} k (t: n_tuple bool n),
    length (enum_tuples' k t) = k.
Proof.
  induction k; simpl; eauto.
Qed.

Lemma length_enum_tuples:
  forall n,
    length (enum_tuples n) = Nat.pow 2 n.
Proof.
  unfold enum_tuples.
  eauto using length_enum_tuples'.
Qed.

Fixpoint code (n: nat) : n_tuple bool n -> nat :=
  match n as n' return n_tuple bool n' -> nat with
  | 0 => fun _ => 0
  | S n =>
    fun t =>
    let '(t, b) := t in
    match b with
    | false => 2 * (code n t)
    | true => S (2 * (code n t))
    end
  end.

Lemma code_nth:
  forall n (x: n_tuple bool n),
    nth_error (enum_tuples n) (code n x) = Some x.
Proof.
  induction n.
  - intros [].
    reflexivity.
  - unfold enum_tuples.
    intros [x b].
    cbn in *.
    destruct b.
Admitted.

Global Program Instance BoolTupleFinite (n: nat): Finite (n_tuple bool n) :=
  {| enum := enum_tuples n |}.
Next Obligation.
Admitted.
Next Obligation.
  eapply nth_error_In.
  eapply code_nth.
Qed.

Lemma unit_type_neq:
  forall T,
    (unit:Type) = T ->
    forall (x y: T),
      x <> y ->
      False.
Proof.
  intros T Ht.
  rewrite <- Ht.
  intros [] [].
  congruence.
Qed.

Lemma n_tuple_diff_neq:
  forall n m,
    n <> m ->
    n_tuple bool n <> n_tuple bool m.
Proof.
  intros.
  eapply TypeNeq.card_neq.
  cbn.
  rewrite !length_enum_tuples.
  intro Hpow.
  eapply PeanoNat.Nat.pow_inj_r in Hpow; auto.
Qed.

Lemma n_tuple_succ_inj:
  forall n m,
    n_tuple bool (1 + n) = n_tuple bool (1 + m) ->
    n_tuple bool n = n_tuple bool m.
Proof.
  intros n m.
  destruct (PeanoNat.Nat.eq_dec n m).
  - subst m.
    eauto.
  - intros.
    exfalso.
    eapply n_tuple_diff_neq; [|eassumption].
    eauto.
Qed.

Lemma n_tuple_inj:
  forall n m,
    n_tuple bool n = n_tuple bool m ->
    n = m.
Proof.
  intros.
  destruct (PeanoNat.Nat.eq_dec n m); auto.
  exfalso.
  eapply n_tuple_diff_neq; eauto.
Qed.
