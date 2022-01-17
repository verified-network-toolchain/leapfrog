
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