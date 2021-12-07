Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.SelfComparison.


Declare ML Module "mirrorsolve".

Module Positive.

  Notation H := (ReadUndef.header + ReadUndef.header).
  Notation A := (Sum.sum ReadUndef.aut ReadUndef.aut).
  Notation conf := (P4automaton.configuration (P4A.interp A)).
  Definition r_states :=
    Eval vm_compute in (Reachability.reachable_states
                          A
                          10
                          ReadUndef.ParseEth
                          ReadUndef.ParseEth).

  Definition top : Relations.rel conf := fun _ _ => True.
  Definition top' : Relations.rel (state_template A) := fun _ _ => True.

  ClearEnvCtors.

  (*
  RegisterEnvCtors
    (ReadUndef.HdrEth, FirstOrderConfRelSimplified.Bits eth_size)
    (ReadUndef.HdrIP, FirstOrderConfRelSimplified.Bits ip_size)
    (ReadUndef.HdrVLAN, FirstOrderConfRelSimplified.Bits vlan_size)
    (ReadUndef.HdrUDP, FirstOrderConfRelSimplified.Bits udp_size).
  *)

  Lemma prebisim_babyip:
    forall q1 q2,
      interp_conf_rel' {| cr_st := {|
                          cs_st1 := {|
                            st_state := inl (inl (ReadUndef.ParseEth));
                            st_buf_len := 0;
                          |};
                          cs_st2 := {|
                            st_state := inl (inr (ReadUndef.ParseEth));
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
                    (mk_init _ _ _ A 10 ReadUndef.ParseEth ReadUndef.ParseEth)
                    q1 q2.
  Proof.
    idtac "running self-comparison positive bisimulation".

    intros.
    set (rel0 := (mk_init _ _ _ A 10 ReadUndef.ParseEth ReadUndef.ParseEth)).
    vm_compute in rel0.
    subst rel0.

    time "build phase" repeat (time "single step" run_bisim top top' r_states).
    time "close phase" close_bisim top'.
  Time Admitted.
End Positive.

Module Negative.

  Notation H := (ReadUndefIncorrect.header + ReadUndefIncorrect.header).
  Notation A := (Sum.sum ReadUndefIncorrect.aut ReadUndefIncorrect.aut).
  Notation conf := (P4automaton.configuration (P4A.interp A)).
  Definition r_states :=
    Eval vm_compute in (Reachability.reachable_states
                          A
                          10
                          ReadUndefIncorrect.ParseEth
                          ReadUndefIncorrect.ParseEth).

  Definition top : Relations.rel conf := fun _ _ => True.
  Definition top' : Relations.rel (state_template A) := fun _ _ => True.

  ClearEnvCtors.

  (*
  RegisterEnvCtors
    (ReadUndefIncorrect.HdrEth, FirstOrderConfRelSimplified.Bits eth_size)
    (ReadUndefIncorrect.HdrIP, FirstOrderConfRelSimplified.Bits ip_size)
    (ReadUndefIncorrect.HdrVLAN, FirstOrderConfRelSimplified.Bits vlan_size)
    (ReadUndefIncorrect.HdrUDP, FirstOrderConfRelSimplified.Bits udp_size).
  *)

  Lemma prebisim_babyip:
    forall q1 q2,
      interp_conf_rel' {| cr_st := {|
                          cs_st1 := {|
                            st_state := inl (inl (ReadUndefIncorrect.ParseEth));
                            st_buf_len := 0;
                          |};
                          cs_st2 := {|
                            st_state := inl (inr (ReadUndefIncorrect.ParseEth));
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
                    (mk_init _ _ _ A 10 ReadUndefIncorrect.ParseEth ReadUndefIncorrect.ParseEth)
                    q1 q2.
  Proof.
    idtac "running self-comparison negative bisimulation".

    intros.
    set (rel0 := (mk_init _ _ _ A 10 ReadUndefIncorrect.ParseEth ReadUndefIncorrect.ParseEth)).
    vm_compute in rel0.
    subst rel0.

    time "build phase" repeat (time "single step" run_bisim top top' r_states).
    Fail time "close phase" close_bisim top'.
  Time Admitted.
End Negative.
