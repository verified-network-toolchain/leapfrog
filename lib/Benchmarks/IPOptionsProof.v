Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.IPOptions.


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

(* Module SelfComparison.

  Notation H := (IPOptionsRef.header + IPOptionsRef.header).
  Notation A := (Sum.sum IPOptionsRef.aut IPOptionsRef.aut).
  Notation conf := (P4automaton.configuration (P4A.interp A)).
  Definition r_states :=
    Eval vm_compute in (Reachability.reachable_states
                          A
                          10
                          IPOptionsRef.Parse0
                          IPOptionsRef.Parse0).

  ClearEnvCtors.

  RegisterEnvCtors
    (IPOptionsRef.Scratch8, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef.Scratch16, FirstOrderConfRelSimplified.Bits 16)
    (  IPOptionsRef.Scratch24, FirstOrderConfRelSimplified.Bits 24)
    (  IPOptionsRef.Scratch32, FirstOrderConfRelSimplified.Bits 32)
    (  IPOptionsRef.Scratch40, FirstOrderConfRelSimplified.Bits 40)
    (  IPOptionsRef.Scratch48, FirstOrderConfRelSimplified.Bits 48)
    (  IPOptionsRef.Scratch56, FirstOrderConfRelSimplified.Bits 56)
    (  IPOptionsRef.T0, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef.L0, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef.V0, FirstOrderConfRelSimplified.Bits 64)
    (  IPOptionsRef.T1, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef.L1, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef.V1, FirstOrderConfRelSimplified.Bits 64)
    (  IPOptionsRef.T2, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef.L2, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef.V2, FirstOrderConfRelSimplified.Bits 64)
    (  IPOptionsRef.T3, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef.L3, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef.V3, FirstOrderConfRelSimplified.Bits 64)
    (  IPOptionsRef.T4, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef.L4, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef.V4, FirstOrderConfRelSimplified.Bits 64)
    (  IPOptionsRef.T5, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef.L5, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef.V5, FirstOrderConfRelSimplified.Bits 64)
    (  IPOptionsRef.T6, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef.L6, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef.V6, FirstOrderConfRelSimplified.Bits 64)
    (  IPOptionsRef.T7, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef.L7, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef.V7, FirstOrderConfRelSimplified.Bits 64)
    (  IPOptionsRef.T8, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef.L8, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef.V8, FirstOrderConfRelSimplified.Bits 64)
    (  IPOptionsRef.T9, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef.L9, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef.V9, FirstOrderConfRelSimplified.Bits 64).

  Lemma prebisim_babyip:
    forall q1 q2,
      interp_conf_rel' {| cr_st := {|
                          cs_st1 := {|
                            st_state := inl (inl (IPOptionsRef.Parse0));
                            st_buf_len := 0;
                          |};
                          cs_st2 := {|
                            st_state := inl (inr (IPOptionsRef.Parse0));
                            st_buf_len := 0;
                          |};
                        |};
                        cr_ctx := BCEmp;
                        cr_rel := btrue;
                    |} q1 q2 ->
    pre_bisimulation A
                     (projT1 r_states)
                     (wp (a := A))
                     []
                     (mk_init _ _ _ A IPOptionsRef.Parse0 IPOptionsRef.Parse0)
                     q1 q2.
  Proof.
    idtac "running ipoptions ref self-comparison bisimulation".

    intros.
    set (rel0 := (mk_init _ _ _ A IPOptionsRef.Parse0 IPOptionsRef.Parse0)).
    vm_compute in rel0.
    subst rel0.

    time "build phase" repeat (time "single step" run_bisim).
    time "close phase" close_bisim.
  Time Admitted.
End SelfComparison. *)

Module SelfComparison.

  Notation H := (IPOptionsRef2.header + IPOptionsRef2.header).
  Notation A := (Sum.sum IPOptionsRef2.aut IPOptionsRef2.aut).
  Notation conf := (P4automaton.configuration (P4A.interp A)).

  Definition r_states :=
    Eval vm_compute in (Reachability.reachable_states
                          A
                          5
                          IPOptionsRef2.Parse0
                          IPOptionsRef2.Parse0).

  (* Definition r_with_len := Eval vm_compute in (length r_states, r_states).

  Print r_with_len. *)

  ClearEnvCtors.

  (*
  RegisterEnvCtors
    (IPOptionsRef5.Scratch8, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef5.Scratch16, FirstOrderConfRelSimplified.Bits 16)
    (  IPOptionsRef5.Scratch24, FirstOrderConfRelSimplified.Bits 24)
    (  IPOptionsRef5.Scratch32, FirstOrderConfRelSimplified.Bits 32)
    (  IPOptionsRef5.Scratch40, FirstOrderConfRelSimplified.Bits 40)
    (  IPOptionsRef5.Scratch48, FirstOrderConfRelSimplified.Bits 48)
    (  IPOptionsRef5.Scratch56, FirstOrderConfRelSimplified.Bits 56)
    (  IPOptionsRef5.T0, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef5.L0, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef5.V0, FirstOrderConfRelSimplified.Bits 64)
    (  IPOptionsRef5.T1, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef5.L1, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef5.V1, FirstOrderConfRelSimplified.Bits 64)
    (  IPOptionsRef5.T2, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef5.L2, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsRef5.V2, FirstOrderConfRelSimplified.Bits 64).
  *)

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
                            st_state := inl (inl (IPOptionsRef2.Parse0));
                            st_buf_len := 0;
                          |};
                          cs_st2 := {|
                            st_state := inl (inr (IPOptionsRef2.Parse0));
                            st_buf_len := 0;
                          |};
                        |};
                        cr_ctx := BCEmp;
                        cr_rel := btrue;
                    |} q1 q2 ->
    pre_bisimulation A
                    (projT1 r_states)
                    (wp (a := A))
                    []
                    (mk_init _ _ _ _ A 5 IPOptionsRef2.Parse0 IPOptionsRef2.Parse0)
                    q1 q2.
  Proof.
    idtac "running ipoptions ref self-comparison bisimulation".

    intros.
    set (rel0 := (mk_init _ _ _ _ A 5 IPOptionsRef2.Parse0 IPOptionsRef2.Parse0)).
    vm_compute in rel0.
    subst rel0.
    clear H.

    match goal with
    | |- pre_bisimulation _ _ _ _ ?G _ _ =>
      hashcons_list G
    end.

    Set Ltac Profiling.



    do 25 ((time "single step" run_bisim);
    match goal with
    | |- pre_bisimulation _ _ _ (?N :: _) _ _ _  =>
      let r := fresh "r" in
      set (r := N)
    | _ => idtac
    end).

    do 25 ((time "single step" run_bisim);
    match goal with
    | |- pre_bisimulation _ _ _ (?N :: _) _ _ _  =>
      let r := fresh "r" in
      set (r := N)
    | _ => idtac
    end).

    do 25 ((time "single step" run_bisim);
    match goal with
    | |- pre_bisimulation _ _ _ (?N :: _) _ _ _  =>
      let r := fresh "r" in
      set (r := N)
    | _ => idtac
    end).

    do 25 ((time "single step" run_bisim);
    match goal with
    | |- pre_bisimulation _ _ _ (?N :: _) _ _ _  =>
      let r := fresh "r" in
      set (r := N)
    | _ => idtac
    end).

    do 25 ((time "single step" run_bisim);
    match goal with
    | |- pre_bisimulation _ _ _ (?N :: _) _ _ _  =>
      let r := fresh "r" in
      set (r := N)
    | _ => idtac
    end).

    do 25 ((time "single step" run_bisim);
    match goal with
    | |- pre_bisimulation _ _ _ (?N :: _) _ _ _  =>
      let r := fresh "r" in
      set (r := N)
    | _ => idtac
    end).

    idtac "150 steps...".


    time "build phase" repeat (time "single step" run_bisim).
    time "close phase" close_bisim.
  Time Admitted.
End SelfComparison.

