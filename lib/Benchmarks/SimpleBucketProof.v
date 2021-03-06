Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.SimpleParsers.

Notation H := (TwoOnesChunk.header + TwoOnesBucket.header).
Notation A := (Sum.sum TwoOnesChunk.aut TwoOnesBucket.aut).
Notation conf := (P4automaton.configuration (P4A.interp A)).

Definition r_states : {r : Reachability.state_pairs A & Reachability.reachable_states_wit TwoOnesChunk.Start TwoOnesBucket.Start r}.
  econstructor.
  unfold Reachability.reachable_states_wit.
  solve_fp_wit.
Defined.

Declare ML Module "mirrorsolve".

(*
RegisterEnvCtors
  (TwoOnesChunk.Bits, FirstOrderConfRelSimplified.Bits 2)
  (TwoOnesBucket.Bits, FirstOrderConfRelSimplified.Bits 2)
  (TwoOnesBucket.Val, FirstOrderConfRelSimplified.Bits 1).
*)

Lemma prebisim_babyip:
  forall q1 q2,
    interp_conf_rel' {| cr_st := {|
                        cs_st1 := {|
                          st_state := inl (inl (TwoOnesChunk.Start));
                          st_buf_len := 0;
                        |};
                        cs_st2 := {|
                          st_state := inl (inr (TwoOnesBucket.Start));
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
                   (mk_init _ _ _ _ A 10 TwoOnesChunk.Start TwoOnesBucket.Start)
                   q1 q2.
Proof.
  idtac "running small bucket bisimulation".

  intros.
  set (rel0 := (mk_init _ _ _ _ A 10 TwoOnesChunk.Start TwoOnesBucket.Start)).
  vm_compute in rel0.
  subst rel0.

  time "build phase" repeat (time "single step" run_bisim).
  time "close phase" close_bisim.
Time Admitted.
