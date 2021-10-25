Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.IPOptions.


Declare ML Module "mirrorsolve".

Ltac hashcons_list xs :=
  match xs with
  | ?x :: ?xs =>
    hashcons_list xs;
    let v := fresh "v" in 
    set (v := x)
    
  | ?x :: nil =>
    let v := fresh "v" in 
    set (v := x)
  | nil =>
    idtac
  end.

Module SelfComparison.
    
  Notation H := (IPOptions32.header + IPOptions32.header).
  Notation A := (Sum.sum IPOptions32.aut IPOptions32.aut).
  Notation conf := (P4automaton.configuration (P4A.interp A)).


  Definition r_states :=
    Eval vm_compute in (Reachability.reachable_states
                          A
                          10
                          IPOptions32.Parse0
                          IPOptions32.Parse0).

  (* Definition r_with_len := Eval vm_compute in (length r_states, r_states).

  Print r_with_len. *)

  Definition top : Relations.rel conf := fun _ _ => True.
  Definition top' : Relations.rel (state_template A) := fun _ _ => True.

  ClearEnvCtors.

  RegisterEnvCtors
    (IPOptions32.Scratch8, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptions32.Scratch16, FirstOrderConfRelSimplified.Bits 16)
    (  IPOptions32.T0, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptions32.L0, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptions32.V0, FirstOrderConfRelSimplified.Bits 24)
    (  IPOptions32.T1, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptions32.L1, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptions32.V1, FirstOrderConfRelSimplified.Bits 24).

  Inductive mark : nat -> Type := M : forall (n: nat), mark n.
    
  Ltac measure_goals := match goal with 
    | |- pre_bisimulation _ _ _ _ ?R _ _ => 
      let x := fresh "rem_goals" in
      pose proof (x := M (length R));
      vm_compute in x;
      match goal with 
      | H : mark ?n |- _ => 
        idtac "remaining goals: " n;
        clear H
      end
    end.

  Lemma prebisim_babyip:
    forall q1 q2,
      interp_conf_rel' {| cr_st := {|
                          cs_st1 := {|
                            st_state := inl (inl (IPOptions32.Parse0));
                            st_buf_len := 0;
                          |};
                          cs_st2 := {|
                            st_state := inl (inr (IPOptions32.Parse0));
                            st_buf_len := 0;
                          |};
                        |};
                        cr_ctx := BCEmp;
                        cr_rel := btrue;
                    |} q1 q2 ->
    pre_bisimulation A
                    (wp r_states)
                    top
                    []
                    (mk_init _ _ _ A 10 IPOptions32.Parse0 IPOptions32.Parse0)
                    q1 q2.
  Proof.
    idtac "running ipoptions ref self-comparison bisimulation".

    intros.
    set (rel0 := (mk_init _ _ _ A 10 IPOptions32.Parse0 IPOptions32.Parse0)).
    vm_compute in rel0.
    subst rel0.
    clear H.

    Set Ltac Profiling.

    (* match goal with 
    | |- pre_bisimulation _ _ _ _ ?G _ _ =>
      hashcons_list G
    end. *)

    (* Set Ltac Profiling. *)



    do 25 ((time "single step" run_bisim top top' r_states);
    match goal with 
    | |- pre_bisimulation _ _ _ (?N :: _) _ _ _  => 
      let r := fresh "r" in 
      set (r := N)
    | _ => idtac
    end).

    do 25 ((time "single step" run_bisim top top' r_states);
    match goal with 
    | |- pre_bisimulation _ _ _ (?N :: _) _ _ _  => 
      let r := fresh "r" in 
      set (r := N)
    | _ => idtac
    end).

    do 25 ((time "single step" run_bisim top top' r_states);
    match goal with 
    | |- pre_bisimulation _ _ _ (?N :: _) _ _ _  => 
      let r := fresh "r" in 
      set (r := N)
    | _ => idtac
    end).

    do 25 ((time "single step" run_bisim top top' r_states);
    match goal with 
    | |- pre_bisimulation _ _ _ (?N :: _) _ _ _  => 
      let r := fresh "r" in 
      set (r := N)
    | _ => idtac
    end).

    do 25 ((time "single step" run_bisim top top' r_states);
    match goal with 
    | |- pre_bisimulation _ _ _ (?N :: _) _ _ _  => 
      let r := fresh "r" in 
      set (r := N)
    | _ => idtac
    end).

    do 25 ((time "single step" run_bisim top top' r_states);
    match goal with 
    | |- pre_bisimulation _ _ _ (?N :: _) _ _ _  => 
      let r := fresh "r" in 
      set (r := N)
    | _ => idtac
    end).

    idtac "150 steps..., quitting...".

    Show Ltac Profile.

 Time Admitted.

End SelfComparison.

