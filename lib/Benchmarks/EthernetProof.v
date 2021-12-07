Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.Ethernet.

Notation H := (Reference.header + Combined.header).
Notation A := RefComb.aut.
Notation conf := (P4automaton.configuration (P4A.interp A)).
Notation start_left := Reference.SPref.
Notation start_right := Combined.Parse.

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
  (Reference.HPref, FirstOrderConfRelSimplified.Bits 64)
  (Reference.HSrc, FirstOrderConfRelSimplified.Bits 48)
  (Reference.HDest, FirstOrderConfRelSimplified.Bits 48)
  (Reference.HProto, FirstOrderConfRelSimplified.Bits 16)
  (Combined.HdrVar, FirstOrderConfRelSimplified.Bits 176).
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
                   (mk_init _ _ _ _ A 200 start_left start_right)
                   q1 q2.
Proof.
  idtac "running ethernet bisimulation".

  intros.
  set (a := A).
  set (rel0 := (mk_init _ _ _ _ _ _ _ _)).
  vm_compute in rel0.
  subst rel0.

  time "build phase" repeat (time "single step" run_bisim top top' r_states).
  time "close phase" close_bisim top'.

Time Admitted.
