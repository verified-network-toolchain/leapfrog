Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.IPOptions.


Declare ML Module "mirrorsolve".

Module SelfComparison.
    
  Notation H := (IPOptions32.header + IPOptions32.header).
  Notation A := (Sum.sum IPOptions32.aut IPOptions32.aut).
  Notation conf := (P4automaton.configuration (P4A.interp A)).

  Definition r_states :=
    Eval vm_compute in (Reachability.reachable_states
                          A
                          5
                          IPOptions32.Parse0
                          IPOptions32.Parse0).

  

  (* Definition r_len := Eval vm_compute in (length r_states). *)

  (* Print r_len. *)

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
                    (mk_init _ _ _ A 5 IPOptions32.Parse0 IPOptions32.Parse0)
                    q1 q2.
  Proof.
    idtac "running ipoptions ref self-comparison bisimulation".

    intros.
    set (rel0 := (mk_init _ _ _ _ _ _ _)).
    vm_compute in rel0.
    subst rel0.
    
    (* set (seven := 7).
    assert (H7 : 7 = seven); [subst seven; reflexivity|]. *)
    set (eight := 8).
    assert (H8 : 8 = eight); [subst eight; reflexivity|].
    (* assert (H8' : Datatypes.S seven = eight); [subst; reflexivity|]. *)
    (* set (fifteen := (Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S eight)))))))).
    assert (H15 : ( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S eight))))))) = fifteen); [subst fifteen; reflexivity|]. *)
    set (sixteen := (Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S eight))))))))).
    assert (H16 : (Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S eight)))))))) = sixteen); [subst sixteen; reflexivity|].
    (* assert (H16' : (Datatypes.S fifteen = sixteen)); [subst; reflexivity|]. *)

    (* try rewrite H7; *)
    try rewrite H8;
    (* try rewrite H15; *)
    try rewrite H16.
    (* try rewrite H16'. *)

    match goal with 
    | |- pre_bisimulation _ _ _ _ ?R _ _ => 
      hashcons_list R
    end.

    Set Ltac Profiling.

    time "build phase" repeat (run_bisim top top' r_states;

    try rewrite H8;
    try rewrite H16;
    
    try match goal with 
    | |- pre_bisimulation _ _ _ (?N :: ?N' :: ?T) _ _ _  => 
      let rs := fresh "rs" in 
      set (rs := N' :: T);
      let r := fresh "r" in 
      set (r := N)
      
    | |- pre_bisimulation _ _ _ (?N :: nil) _ _ _  => 
      let r := fresh "r" in 
      set (r := N)
    end).


    Show Ltac Profile.
    Reset Ltac Profile.

    time "close phase" close_bisim top'.

    Show Ltac Profile.
    Reset Ltac Profile.

 Time Admitted.

End SelfComparison.

Module SpecCompare.
    
  Notation H := (IPOptions32.header + IPOptionsSpec32.header).
  Notation A := (Sum.sum IPOptions32.aut IPOptionsSpec32.aut).
  Notation conf := (P4automaton.configuration (P4A.interp A)).


  Definition r_states :=
    Eval vm_compute in (Reachability.reachable_states
                          A
                          5
                          IPOptions32.Parse0
                          IPOptionsSpec32.Parse0).

  

  (* Definition r_len := Eval vm_compute in (length r_states).

  Print r_len. *)

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
    (  IPOptions32.V1, FirstOrderConfRelSimplified.Bits 24)
    (IPOptionsSpec32.Scratch8, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsSpec32.Scratch16, FirstOrderConfRelSimplified.Bits 16)
    (  IPOptionsSpec32.Scratch24, FirstOrderConfRelSimplified.Bits 24)
    (  IPOptionsSpec32.T0, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsSpec32.L0, FirstOrderConfRelSimplified.Bits 8)
    (  IPOptionsSpec32.V, FirstOrderConfRelSimplified.Bits 16).

  

  Lemma prebisim_babyip:
    forall q1 q2,
      interp_conf_rel' {| cr_st := {|
                          cs_st1 := {|
                            st_state := inl (inl (IPOptions32.Parse0));
                            st_buf_len := 0;
                          |};
                          cs_st2 := {|
                            st_state := inl (inr (IPOptionsSpec32.Parse0));
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
                    (mk_init _ _ _ A 5 IPOptions32.Parse0 IPOptionsSpec32.Parse0)
                    q1 q2.
  Proof.
    idtac "running ipoptions small specialized bisimulation".

    intros.
    set (rel0 := (mk_init _ _ _ _ _ _ _)).
    vm_compute in rel0.
    subst rel0.
    
    (* set (seven := 7).
    assert (H7 : 7 = seven); [subst seven; reflexivity|]. *)
    set (eight := 8).
    assert (H8 : 8 = eight); [subst eight; reflexivity|].
    (* assert (H8' : Datatypes.S seven = eight); [subst; reflexivity|]. *)
    (* set (fifteen := (Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S eight)))))))).
    assert (H15 : ( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S eight))))))) = fifteen); [subst fifteen; reflexivity|]. *)
    set (sixteen := (Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S eight))))))))).
    assert (H16 : (Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S eight)))))))) = sixteen); [subst sixteen; reflexivity|].
    (* assert (H16' : (Datatypes.S fifteen = sixteen)); [subst; reflexivity|]. *)

    (* try rewrite H7; *)
    try rewrite H8;
    (* try rewrite H15; *)
    try rewrite H16.
    (* try rewrite H16'. *)

    match goal with 
    | |- pre_bisimulation _ _ _ _ ?R _ _ => 
      hashcons_list R
    end.

    Set Ltac Profiling.

    time "build phase" repeat (run_bisim top top' r_states;

    try rewrite H8;
    try rewrite H16;
    
    try match goal with 
    | |- pre_bisimulation _ _ _ (?N :: ?N' :: ?T) _ _ _  => 
      let rs := fresh "rs" in 
      set (rs := N' :: T);
      let r := fresh "r" in 
      set (r := N)
      
    | |- pre_bisimulation _ _ _ (?N :: nil) _ _ _  => 
      let r := fresh "r" in 
      set (r := N)
    end).


    Show Ltac Profile.
    Reset Ltac Profile.

    time "close phase" close_bisim top'.

    Show Ltac Profile.
    Reset Ltac Profile.

 Time Admitted.

End SpecCompare.