Require Import Coq.Classes.EquivDec.
Import List.ListNotations.

Section DepEnv.
  Variable (I: Type).
  Context `{I_eq_dec: EquivDec.EqDec I eq}.
  Variable (K: I -> Type).
  Context `{K_eq_dec: forall i, EquivDec.EqDec (K i) eq}.
  Variable (V: I -> Type).

  Definition binding :=
    {i: I & K i & V i}.

  Definition t := list binding.

  Fixpoint find {i} (k: K i) (e: t) : option (V i).
    destruct e as [ | [j k' v] e'].
    - exact None.
    - destruct (i == j).
      + unfold "===" in e.
        subst j.
        destruct (k == k').
        * exact (Some v).
        * exact (find i k e').
      + exact (find i k e').
  Defined.

  Definition bind {i} (k: K i) (v: V i) (e: t) : list binding :=
    existT2 _ _ i k v :: e.

End DepEnv.
