Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.SimpleParsers.

Notation A := OneZero.aut.
Notation conf := (P4automaton.configuration (P4A.interp A)).

Definition r_states :=
  Eval vm_compute in (Reachability.reachable_states
                        OneZero.aut
                        200
                        ParseOne.Start
                        ParseZero.Start).

Definition top : Relations.rel conf := fun _ _ => True.
Definition top' : Relations.rel (state_template A) := fun _ _ => True.

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
      pre_bisimulation  A
                        (wp r_states)
                        top
                        []
                        (mk_init _ _ _ _ A 200 ParseOne.Start ParseZero.Start)
                        q1 q2.
Proof.
  intros.
  set (rel0 := (mk_init _ _ _ _ _ _ _ _)).
  vm_compute in rel0.
  subst rel0.
  time "build phase" repeat (time "single step" run_bisim top top' r_states).
  Fail time "close phase" close_bisim top'.
Abort.
