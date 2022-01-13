
Section FuelFP.
  Variable (A: Type).
  Variable (f: A -> A).

  Fixpoint iter (n: nat) (a: A) : A := 
    match n with 
    | 0 => a
    | S n' => f (iter n' a)
    end.

  Variable (eqb: A -> A -> bool).

  Fixpoint iter' (n: nat) (a: A) : A := 
    match n with 
    | 0 => a
    | S n' => 
      let nxt := f a in 
      if eqb nxt a then nxt else f (iter' n' a)
    end.

  Variable (eqb_sound: forall x, eqb (f x) x = true <-> (f x) = x).

  Lemma iter_iter' : 
    forall n a,
    iter n a = iter' n a.
  Proof.
    intros.
    induction n.
    - simpl. reflexivity.
    - unfold iter; fold iter.
      unfold iter'; fold iter'.
      pose proof (@eqb_sound a).
      destruct (eqb _ _) eqn:?.
      + destruct H as [H' _].
        erewrite H'; trivial.
        erewrite IHn.

        destruct n; simpl iter'; [eapply H'; trivial|].

        specialize (@eqb_sound a).
        destruct eqb_sound as [_ H''].
        erewrite H''; erewrite H'; trivial.
        eapply H'; trivial.
      + erewrite IHn; trivial.
  Qed.

End FuelFP.


Section ExactFP.
  Variable (A: Type).
  Variable (f: A -> A).

  Definition fp := {x | f x = x}.

  Inductive fp_wit : A -> A -> Type := 
  | FPDone : forall x, 
    f x = x -> fp_wit x x
  | FPIter : forall x y,
    fp_wit (f x) y -> fp_wit x y.

  (* extract the final fp out from a construction of its fp-ness *)
  Fixpoint wit_conv {x y} (wit: fp_wit x y) : fp := 
    match wit with 
    | FPDone _ pf => exist _ _ pf
    | FPIter _ _ wit' => wit_conv wit'
    end.
  
End ExactFP.

Ltac solve_fp_wit := 
  repeat (
    match goal with 
    | |- fp_wit _ _ _ _ => 
      eapply FPDone;
      simpl;
      trivial
    | |- fp_wit _ _ ?X _ => 
      econstructor;
      set (foo := X);
      vm_compute in foo;
      subst foo
    end
  ).

Definition collatz (n: nat) := 
  match n with
  | 1 => 1
  | n => 
    if Nat.even n then Nat.div n 2 else 3 * n + 1
  end.

Definition collatz_10 : fp _ collatz.
  evar (n: nat).
  assert (fp_wit _ collatz 10 n).
  solve_fp_wit.
  subst n.
  eapply FPDone.
  compute.
  trivial.
  subst n.
  simpl collatz in X.
  eapply wit_conv.
  exact X.
Defined.
