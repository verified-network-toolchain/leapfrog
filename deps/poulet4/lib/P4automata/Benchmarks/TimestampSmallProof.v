Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.Timestamp.

Notation H := (TimestampRefSmall.header + TimestampSpecSmall.header).
Notation A := (Sum.sum TimestampRefSmall.aut TimestampSpecSmall.aut).
Notation conf := (P4automaton.configuration (P4A.interp A)).
Notation start_left := TimestampRefSmall.Start.
Notation start_right := TimestampSpecSmall.Start.

Definition r_states :=
  Eval vm_compute in (Reachability.reachable_states
                        A
                        200
                        start_left
                        start_right).

Definition top : Relations.rel conf := fun _ _ => True.
Definition top' : Relations.rel (state_template A) := fun _ _ => True.

Declare ML Module "mirrorsolve".

(*
RegisterEnvCtors
  (TimestampRefSmall.Len, FirstOrderConfRelSimplified.Bits 2)
  (TimestampRefSmall.Pref1, FirstOrderConfRelSimplified.Bits 8)
  (TimestampRefSmall.Pref2, FirstOrderConfRelSimplified.Bits 16)
  (TimestampRefSmall.Timestamps, FirstOrderConfRelSimplified.Bits 24)
  (TimestampSpecSmall.Len, FirstOrderConfRelSimplified.Bits 2)
  (TimestampSpecSmall.T1, FirstOrderConfRelSimplified.Bits 8)
  (TimestampSpecSmall.T2, FirstOrderConfRelSimplified.Bits 8)
  (TimestampSpecSmall.T3, FirstOrderConfRelSimplified.Bits 8).
*)

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
                   (mk_init _ _ _ A 200 start_left start_right)
                   q1 q2.
Proof.
  idtac "running small timestamp bisimulation".

  intros.
  set (a := A).
  set (rel0 := (mk_init _ _ _ _ _ _ _)).
  vm_compute in rel0.
  subst rel0.

  time "build phase" repeat (time "single step" run_bisim top top' r_states).
  time "close phase" close_bisim top'.

Time Admitted.
