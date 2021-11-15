Require Import Coq.Classes.EquivDec.
Import List.ListNotations.

Section DepEnv.
  Variable (I: Type).
  Variable (K: I -> Type).
  Variable (V: I -> Type).

  Definition binding :=
    {i: I & K i & V i}.
  Definition key :=
    {i: I & K i}.

  Context `{K_eq_dec: EquivDec.EqDec key eq}.

  Definition t := list binding.

  Fixpoint find {i} (k: K i) (e: t) : option (V i).
  Proof.
    destruct e as [ | [j k' v] e'].
    - exact None.
    - destruct (existT K i k == existT K j k').
      + inversion e; subst.
        exact (Some v).
      + exact (find i k e').
  Defined.

  Definition bind {i} (k: K i) (v: V i) (e: t) : list binding :=
    existT2 _ _ i k v :: e.

End DepEnv.
