Require Import Coq.Lists.List.
Require Import Coq.Program.Program.
Import ListNotations.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Arith.PeanoNat.

(* based roughly on stdpp.finite *)
Class Finite (A: Type) `{EqDec A Logic.eq} := {
  enum: list A;
  NoDup_enum: NoDup enum;
  elem_of_enum: forall (x: A), In x enum
}.
Global Arguments enum _ {_} {_} {_}.

Global Program Instance UnitFinite: Finite unit :=
  {| enum := [tt] |}.
Next Obligation.
  constructor; eauto.
  constructor.
Qed.
Next Obligation.
  destruct x.
  auto.
Qed.

Lemma NoDup_app :
  forall A (l l': list A),
    NoDup l ->
    NoDup l' ->
    (forall x, In x l -> ~ In x l') ->
    (forall x, In x l' -> ~ In x l) ->
    NoDup (l ++ l').
Proof.
  induction l; destruct l'; simpl; autorewrite with list; auto.
  intros.
  constructor.
  + intro.
    inversion H; subst.
    apply in_app_or in H3.
    destruct H3; auto.
    eapply H2; eauto with datatypes.
  + eapply IHl; eauto with datatypes.
    * inversion H; auto.
    * intuition eauto with datatypes.
Qed.

Lemma NoDup_map:
  forall A B (f: A -> B) l,
    (forall x y, f x = f y -> x = y) ->
    NoDup l ->
    NoDup (map f l).
Proof.
  intros.
  induction l; simpl; constructor.
  - intro Hin.
    apply in_map_iff in Hin.
    destruct Hin as [x [Heq Hin]].
    apply H in Heq.
    subst.
    inversion H0.
    congruence.
  - inversion H0.
    eauto.
Qed.

Global Program Instance SumFinite A B `{Finite A} `{Finite B} : Finite (A + B) :=
  {| enum := List.map inl (enum A) ++ List.map inr (enum B) |}.
Next Obligation.
  eapply NoDup_app; eauto.
  - eapply NoDup_map; try congruence.
    apply NoDup_enum.
  - eapply NoDup_map; try congruence.
    apply NoDup_enum.
  - destruct x; intros Hin Hnin;
      apply in_map_iff in Hnin;
      apply in_map_iff in Hin;
      firstorder congruence.
  - destruct x; intros Hin Hnin;
      apply in_map_iff in Hnin;
      apply in_map_iff in Hin;
      firstorder congruence.
Qed.
Next Obligation.
  destruct x.
  - eapply in_or_app.
    left; eapply in_map; eapply elem_of_enum.
  - eapply in_or_app.
    right; eapply in_map; eapply elem_of_enum.
Qed.

Lemma NoDup_prod:
  forall A B (l1: list A) (l2: list B),
    NoDup l1 ->
    NoDup l2 ->
    NoDup (list_prod l1 l2).
Proof.
  induction l1; intros.
  - constructor.
  - simpl.
    apply NoDup_app.
    + apply NoDup_map; auto.
      intros.
      now inversion H1.
    + apply IHl1; auto.
      now inversion H.
    + intros.
      rewrite in_map_iff in H1.
      destruct x.
      destruct H1 as [? [? ?]].
      inversion H1; subst.
      inversion H.
      contradict H5.
      apply in_prod_iff in H5.
      intuition.
    + intros.
      inversion_clear H.
      contradict H2.
      apply in_map_iff in H2.
      destruct H2 as [? [? ?]].
      subst.
      apply in_prod_iff in H1.
      intuition.
Qed.

Global Program Instance ProdFinite A B `{Finite A} `{Finite B} : Finite (A * B) :=
  {| enum := List.list_prod (enum A) (enum B) |}.
Next Obligation.
  apply NoDup_prod; apply NoDup_enum.
Qed.

Global Program Instance DepProdEqDec
  (A: Type)
  (f: A -> Type)
  `{EqDec A eq}
  `{forall a, EqDec (f a) eq}: EqDec {a: A & f a} eq.
Next Obligation.
  destruct (x == y).
  - unfold equiv in e; subst.
    destruct (X0 == X).
    + unfold equiv in e; subst.
      now left.
    + right; intro.
      unfold equiv, complement in c.
      contradict c.
      intuition.
  - right; intro.
    inversion H1.
    contradiction.
Qed.

Global Program Instance DepProdFinite
  A
  (f: A -> Type)
  `{Finite A}
  `{EqDec A}
  `{forall a, EqDec (f a) eq}
  `{forall a, Finite (f a)}
  : Finite {a : A & f a}
:=
  {| enum := flat_map (fun a => map (existT f a) (enum (f a))) (enum A) |}.
Next Obligation.
  induction NoDup_enum.
  - simpl; constructor.
  - simpl.
    apply NoDup_app; auto.
    + apply NoDup_map.
      * intros.
        intuition.
      * apply H3.
    + intros.
      contradict H4.
      rewrite in_flat_map_Exists, Exists_exists in H4.
      destruct H4 as [? [? ?]].
      rewrite in_map_iff in *.
      destruct H5 as [? [? ?]].
      destruct H6 as [? [? ?]].
      rewrite <- H5 in H6.
      now inversion H6.
    + intros.
      contradict H4.
      rewrite in_map_iff in H4.
      destruct H4 as [? [? ?]].
      rewrite in_flat_map_Exists, Exists_exists in H5.
      destruct H5 as [? [? ?]].
      rewrite in_map_iff in H7.
      destruct H7 as [? [? ?]].
      rewrite <- H7 in H4.
      inversion H4.
      congruence.
Qed.

Global Program Instance FinDepProdFinite
  A
  (f: A -> Type)
  `{Finite { a: A | inhabited (f a) }}
  `{EqDec { a: A | inhabited (f a) }}
  `{forall a, EqDec (f a) eq}
  `{forall a, Finite (f a)}
  : forall a, Finite (f a)
.
Next Obligation.
  apply in_flat_map.
  exists x; split.
  - specialize (H3 x).
    apply H0.
  - apply in_map_iff.
    exists X.
    split.
    + f_equal.
    + apply H3.
Qed.
Next Obligation.
  apply H3.
Qed.

Ltac solve_finiteness :=
  econstructor; [
    idtac |
    intros;
    dependent destruction x;
    repeat (apply List.in_eq || apply List.in_cons)
  ];
  repeat constructor;
  repeat match goal with
         | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
         | |- ~ List.In _ [] => apply List.in_nil
         | |- ~ List.In _ (_ :: _) => unfold not; intros
         | H: List.In _ (_::_) |- _ => inversion H; clear H
         | _ => discriminate
         end.

Ltac solve_indexed_finiteness n indices :=
  match indices with
  | ?index :: ?indices =>
    destruct (Nat.eq_dec n index); [
      subst; solve_finiteness |
      solve_indexed_finiteness n indices
    ]
  | nil =>
    econstructor; [
      apply List.NoDup_nil |
      intros; dependent destruction x; contradiction
    ];
    match goal with |- ?G => idtac G end;
    dependent destruction x;
    contradiction
  end.

Ltac solve_eqdec :=
    unfold EquivDec.EqDec; intros;
    dependent destruction x; dependent destruction y;
    (left; congruence) || (right; congruence).
