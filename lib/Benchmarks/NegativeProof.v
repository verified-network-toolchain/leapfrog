Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.SimpleParsers.

Notation A := OneZero.aut.
Notation conf := (P4automaton.configuration (P4A.interp A)).

Definition r_states : {r : Reachability.state_pairs A & Reachability.reachable_states_wit ParseOne.Start ParseZero.Start r}.
  econstructor.
  unfold Reachability.reachable_states_wit.
  solve_fp_wit.
Defined.

Declare ML Module "mirrorsolve".

(*
RegisterEnvCtors
  (ParseOne.Bit, FirstOrderConfRelSimplified.Bits 1)
  (ParseZero.Bit, FirstOrderConfRelSimplified.Bits 1).
*)

(* These parsers are different, this proof should fail *)
Goal
  forall q1 q2,
    interp_conf_rel' {|
      cr_st := {|
        cs_st1 := {|
          st_state := inl (inl (ParseOne.Start));
          st_buf_len := 0;
        |};
        cs_st2 := {|
          st_state := inl (inr (ParseZero.Start));
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
                       (mk_init _ _ _ _ A ParseOne.Start ParseZero.Start)
                       q1 q2.
Proof.
  intros.
  set (rel0 := (mk_init _ _ _ _ _ _ _)).
  vm_compute in rel0.
  subst rel0.
  time "build phase" repeat (time "single step" run_bisim).
  Fail time "close phase" close_bisim.
Abort.
