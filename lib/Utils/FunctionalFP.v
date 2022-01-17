
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


End ExactFP.

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