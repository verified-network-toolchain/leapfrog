Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.TCAMSimple.


Notation H := (VerySimple.header + Optimized.header).
Notation A := (Sum.sum VerySimple.aut Optimized.aut).
Notation conf := (P4automaton.configuration (P4A.interp A)).
Notation start_left := VerySimple.Ethernet.
Notation start_right := Optimized.State_0.

Require Import Coq.Arith.PeanoNat.

Definition r_states : {r : Reachability.state_pairs A & Reachability.reachable_states_wit start_left start_right r}.
  econstructor.
  unfold Reachability.reachable_states_wit.
  solve_fp_wit.
Defined.

Declare ML Module "mirrorsolve".

SetSMTSolver "cvc4".

Lemma prebisim_incremental_sep:
  forall q1 q2,
    interp_conf_rel' {| cr_st := {|
                        cs_st1 := {|
                          st_state := inl (inl (start_left));
                          st_buf_len := 0;
                        |};
                        cs_st2 := {|
                          st_state := inl (inr (start_right));
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
                   (mk_init _ _ _ _ A reachable_states_len start_left start_right)
                   q1 q2.
Proof.
  idtac "running tcam very simple bisimulation".

  intros.
  set (rel0 := (mk_init _ _ _ _ _ _ _ _)).
  vm_compute in rel0.
  subst rel0.

  time "build phase" repeat (time "single step" run_bisim).
  time "close phase" close_bisim.
Time Admitted.
