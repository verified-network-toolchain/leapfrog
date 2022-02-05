Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.SmallFilter.


Notation H := (IncrementalBits.header + BigBits.header).
Notation A := IncrementalSeparate.aut.
Notation conf := (P4automaton.configuration (P4A.interp A)).

Definition r_states : {r : Reachability.state_pairs A & Reachability.reachable_states_wit IncrementalBits.Start BigBits.Parse r}.
  econstructor.
  unfold Reachability.reachable_states_wit.
  solve_fp_wit.
Defined.

Definition top : Relations.rel conf :=
  fun q1 q2 => List.In (conf_to_state_template q1, conf_to_state_template q2) (projT1 r_states).

Definition top' : Relations.rel (state_template A) :=
  fun q1 q2 => List.In (q1, q2) (projT1 r_states).


Declare ML Module "mirrorsolve".

(*
RegisterEnvCtors
  (IncrementalBits.Pref, FirstOrderConfRelSimplified.Bits 1)
  (IncrementalBits.Suf, FirstOrderConfRelSimplified.Bits 1)
  (BigBits.Pref, FirstOrderConfRelSimplified.Bits 1)
  (BigBits.Suf, FirstOrderConfRelSimplified.Bits 1).
*)


Lemma prebisim_incremental_sep:
  forall q1 q2,
    interp_conf_rel' {| cr_st := {|
                        cs_st1 := {|
                          st_state := inl (inl (IncrementalBits.Start));
                          st_buf_len := 0;
                        |};
                        cs_st2 := {|
                          st_state := inl (inr (BigBits.Parse));
                          st_buf_len := 0;
                        |};
                      |};
                      cr_ctx := BCEmp;
                      cr_rel := btrue;
                   |} q1 q2 ->
  pre_bisimulation A
                   (wp (projT1 r_states))
                   top
                   []
                   (mk_init _ _ _ _ A IncrementalBits.Start BigBits.Parse)
                   q1 q2.
Proof.
  idtac "running smallfilter bisimulation".

  intros.
  set (rel0 := (mk_init _ _ _ _ _ _ _)).
  vm_compute in rel0.
  subst rel0.

  time "build phase" repeat (time "single step" run_bisim top top' (projT1 r_states)).
  time "close phase" close_bisim'' top' r_states.
Time Admitted.
