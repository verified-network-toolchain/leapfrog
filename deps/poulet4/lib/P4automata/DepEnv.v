Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Poulet4.FinType.
From Poulet4.P4automata Require Import FirstOrder.
Import List.ListNotations.

Section DepEnv.
  Variable (I: Type).
  Variable (K: I -> Type).
  Definition K' := {n: I & K n}.
  Context `{K'_eq_dec: EquivDec.EqDec K' eq}.
  Context `{K'_finite: @Finite K' _ K'_eq_dec}.
  Variable (V: I -> Type).

  Definition keylist : list K' :=
    @enum _ _ _ K'_finite.

  Definition t: Type :=
    HList.t (fun k => (V (projT1 k))) keylist.

  Definition get' (k: K') (e: t) : V (projT1 k) :=
    HList.get k (elem_of_enum k) e.

  Definition get {i: I} (k: K i) : t -> V i :=
    get' (existT K i k).

  Definition bind' (k: K') (v: V (projT1 k)) (e: t) : t :=
    HList.bind k v (elem_of_enum k) e.

  Definition bind {i: I} (k: K i) : V i -> t -> t :=
    bind' (existT K i k).

  Definition init (f: forall i, V i) : t :=
    HList.mapl (fun a => f (projT1 a)) keylist.

  Lemma env_extensionality':
    forall e e': t,
      (forall k, get' k e = get' k e') ->
      e = e'.
  Proof.
    intros.
    eapply HList.get_extensionality.
    - apply K'_finite.
    - intros.
      unfold get' in H.
      assert (pf = elem_of_enum k) by apply proof_irrelevance.
      subst pf.
      eapply H.
  Qed.

  Lemma env_extensionality:
    forall e e': t,
      (forall i (k: K i), get k e = get k e') ->
      e = e'.
  Proof.
    intros.
    eapply env_extensionality'.
    intros [i k].
    eauto.
  Qed.
  
End DepEnv.
