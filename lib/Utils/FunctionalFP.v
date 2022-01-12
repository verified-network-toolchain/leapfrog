
Section FunctionalFP.
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

  Variable (eqb_sound: forall a a', eqb a a' = true <-> a = a').

  Lemma iter_iter' : 
    forall n a,
    iter n a = iter' n a.
  Proof.
    intros.
    induction n.
    - simpl. reflexivity.
    - unfold iter; fold iter.
      unfold iter'; fold iter'.
      pose proof (@eqb_sound (f a) a).
      destruct (eqb _ _) eqn:?.
      + destruct H as [H' _].
        erewrite H'; trivial.
        erewrite IHn.

        destruct n; simpl iter'; [eapply H'; trivial|].

        specialize (@eqb_sound (f a) a).
        destruct eqb_sound as [_ H''].
        erewrite H''; erewrite H'; trivial.
        eapply H'; trivial.
      + erewrite IHn; trivial.
  Qed.

End FunctionalFP.