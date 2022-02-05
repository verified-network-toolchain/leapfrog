Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.IPOptions.
Require Import Poulet4.P4automata.Benchmarks.Timestamp.

Notation H := (IPOptionsRef63.header + TimestampSpec3.header).
Notation A := (Sum.sum IPOptionsRef63.aut TimestampSpec3.aut).
Notation conf := (P4automaton.configuration (P4A.interp A)).
Notation start_left := IPOptionsRef63.Parse0.
Notation start_right := TimestampSpec3.Parse0.


Definition r_states' := (Reachability.reachable_states
                          A
                          9
                          start_left
                          start_right).

Definition r_states := Eval vm_compute in r_states'.

Definition top : Relations.rel conf :=
  fun q1 q2 => List.In (conf_to_state_template q1, conf_to_state_template q2) r_states.

Definition top' : Relations.rel (state_template A) :=
  fun q1 q2 => List.In (q1, q2) r_states.

Lemma r_states_conv:
  r_states = r_states'.
Admitted.

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
                   (wp r_states)
                   top
                   []
                   (mk_init _ _ _ A 9 start_left start_right)
                   q1 q2.
Proof.
  idtac "running timestamp three bisimulation".
  intros.
  set (rel0 := (mk_init _ _ _ _ _ _ _)).
  vm_compute in rel0.
  subst rel0.

  time "build phase" repeat (time "single step" run_bisim top top' r_states).
  time "close phase" close_bisim' top top' r_states_conv.

Time Admitted.
