Require Import Coq.Classes.EquivDec.
Import List.ListNotations.

Section DepEnv.
  Variable (K: Type).
  Variable (V: K -> Type).
  Context `{K_eq_dec: EquivDec.EqDec K eq}.

  Definition binding :=
    {k: K & V k}.

  Definition t := list binding.

  Fixpoint find (k: K) (e: t) : option (V k).
  Proof.
    destruct e as [ | [k' v] e'].
    - exact None.
    - destruct (k == k').
      + unfold "===" in e.
        rewrite <- e in v.
        exact (Some v).
      + exact (find k e').
  Defined.

  Definition bind (k: K) (v: V k) (e: t) : list binding :=
    existT _ k v :: e.

End DepEnv.
