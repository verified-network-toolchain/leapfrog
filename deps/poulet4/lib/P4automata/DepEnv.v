Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Poulet4.FinType.
From Poulet4.P4automata Require Import FirstOrder.
Import List.ListNotations.

Section DepEnv.
  Variable (K: Type).
  Context `{K_eq_dec: EquivDec.EqDec K eq}.
  Context `{K_finite: @Finite K _ K_eq_dec}.
  Variable (V: K -> Type).

  Definition K' := {k: K & V k}.

  Definition t: Type :=
    HList.t V (enum K).

  Definition get (k: K) (e: t) : V k :=
    HList.get k (elem_of_enum k) e.

  Definition bind (k: K) (v: V k) (e: t) : t :=
    HList.bind k v (elem_of_enum k) e.

  Definition init (f: forall k, V k) : t :=
    HList.mapl (fun k => f k) (enum K).

  Lemma env_extensionality:
    forall e e': t,
      (forall k, get k e = get k e') ->
      e = e'.
  Proof.
    intros.
    eapply HList.get_extensionality.
    - apply K_finite.
    - intros.
      unfold get in H.
      erewrite HList.get_proof_irrelevance; symmetry.
      erewrite HList.get_proof_irrelevance; symmetry.
      apply H.
  Qed.

End DepEnv.
