
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

  Lemma fp_wit_converges: 
    forall x y z,
      fp_wit x y -> 
      fp_wit x z -> 
      y = z.
  Proof.
    intros.
    induction X; induction X0; trivial.
    - erewrite <- e.
      eapply IHX0.
      erewrite e.
      trivial.
    - eapply IHX.
      erewrite e.
      constructor.
      trivial.
    - eauto.
  Qed.

  Inductive func_iter : A -> A -> Type := 
    | FIZ : forall x, func_iter x x
    | FIS : forall x y, 
      func_iter (f x) y ->
      func_iter x y.

  Variable (P: A -> Prop).
  Variable (a: A).
  Variable (Pbase: P a).
  Variable (Prec: 
    forall x, P x -> P (f x)
  ).

  Lemma func_iter_rec' : 
    forall a', 
      func_iter a a' -> 
      P a'.
  Proof.
    intros.
    induction X; [trivial|].
    eauto.
  Qed.
  
  
  Lemma func_iter_extend : forall x y z, 
    func_iter x y -> 
    func_iter y z -> 
    func_iter x z.
  Proof.
    intros.
    generalize X0.
    generalize z.
    clear X0.
    clear z.
    induction X.
    - intros. trivial.
    - intros.
      constructor.
      eauto.
  Qed.

  Lemma func_iter_conv:
    forall x y (fi: func_iter x y),
      f y = y ->
      fp_wit x y.
  Proof.
    intros x y fi ?.

    induction fi; [constructor; trivial|].
    eapply FPIter.
    eauto.
  Qed.

  Fixpoint func_iter_depth {x y} (fi: func_iter x y) : nat := 
    match fi with 
    | FIZ _ => 0
    | FIS _ _ fi' => S (func_iter_depth fi')
    end.

  Fixpoint iter (fuel: nat) x := 
    match fuel with 
    | 0 => x 
    | S n => iter n (f x)
    end.

  Lemma func_iter_depth_fuel n: 
    forall x y (fi: func_iter x y),
      func_iter_depth fi = n -> 
      iter n x = y.
  Proof.
    induction n; intros.
    - destruct fi eqn:?.
      * exact eq_refl.
      * simpl in H.
        inversion H. 
    - unfold iter. fold iter.
      destruct fi eqn:?.
      * inversion H.
      * eapply IHn.
        unfold func_iter_depth in H.
        fold (func_iter_depth f0) in H.
        assert (func_iter_depth f0 = n) by (inversion H; exact eq_refl).
        exact H0.
  Qed.

End ExactFP.

Section ListFP.
  Variable (T: Type).
  Variable (f: list T -> list T).

  Require Import Coq.Lists.List.

  Variable (f_mono: 
    forall xs, 
    List.NoDup xs -> 
      exists ys,
      f xs = ys ++ xs
  ).

  Lemma f_incl_fp:
    (forall xs, List.NoDup (f xs)) ->
    forall xs,
      NoDup xs ->
      List.incl (f xs) xs -> 
      f xs = xs.
  Proof.
    intros.
    specialize (f_mono xs H0).
    specialize (H xs).
    destruct f_mono as [pref Hpref].
    clear f_mono.
    inversion H; destruct pref.
    - simpl in Hpref.
      erewrite <- Hpref.
      trivial.
    - exfalso.
      erewrite <- H3 in *.
      inversion Hpref.
    - simpl in Hpref.
      erewrite H2.
      trivial.
    - assert (t = x).
      + erewrite Hpref in H2.
        inversion H2.
        exact eq_refl.
      + subst t.
        unfold incl in H1.
        assert (In x xs) by (
          eapply H1;
          erewrite <- H2;
          left;
          exact eq_refl
        ).
        assert (l = pref ++ xs) by (
          erewrite Hpref in H2;
          inversion H2;
          exact eq_refl
        ).
        subst.
        exfalso.
        eapply H3.
        eapply in_or_app.
        right; trivial.
  Qed.
End ListFP.

Ltac solve_fp_wit := 
  let init_v := fresh "v" in
  match goal with 
  | |- fp_wit _ _ _ ?x =>
    set (init_v := x)
  end;
  repeat (
    match goal with 
    | |- fp_wit _ _ ?X _ => 
      econstructor;
      let iter_v := fresh "v'" in 
      set (iter_v := X);
      vm_compute in iter_v;
      subst iter_v
    end
  );
  subst init_v;
  eapply FPDone;
  exact eq_refl.
  

Definition collatz (n: nat) := 
  match n with
  | 1 => 1
  | n => 
    if Nat.even n then Nat.div n 2 else 3 * n + 1
  end.

Definition collatz_10 : {n & fp_wit _ collatz 10 n}.
  econstructor.
  solve_fp_wit.
Defined.

Definition collatz_10_16 : 
  func_iter _ collatz 10 16.
  repeat constructor.
Defined.