Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.BabyIP.

Notation H := (BabyIP1.header + BabyIP2.header).
Notation A := BabyIP.aut.
Notation conf := (P4automaton.configuration (P4A.interp A)).
Definition r_states' := (Reachability.reachable_states_one
                        BabyIP.aut
                        200
                        BabyIP1.Start
                        BabyIP2.Start).

Definition r_states := Eval vm_compute in r_states'.

Definition top : Relations.rel conf :=
  fun q1 q2 => List.In (conf_to_state_template q1, conf_to_state_template q2) r_states.

Definition top' : Relations.rel (state_template A) :=
  fun q1 q2 => List.In (q1, q2) r_states.

Lemma r_states_conv:
  r_states = r_states'.
Admitted.

Declare ML Module "mirrorsolve".

(*
RegisterEnvCtors
  (BabyIP1.HdrIP, FirstOrderConfRelSimplified.Bits 20)
  (BabyIP1.HdrUDP, FirstOrderConfRelSimplified.Bits 20)
  (BabyIP1.HdrTCP, FirstOrderConfRelSimplified.Bits 28)
  (BabyIP2.HdrCombi, FirstOrderConfRelSimplified.Bits 40)
  (BabyIP2.HdrSeq, FirstOrderConfRelSimplified.Bits 8).
*)

Lemma prebisim_babyip:
  forall q1 q2,
    interp_conf_rel' {| cr_st := {|
                        cs_st1 := {|
                          st_state := inl (inl (BabyIP1.Start));
                          st_buf_len := 0;
                        |};
                        cs_st2 := {|
                          st_state := inl (inr (BabyIP2.Start));
                          st_buf_len := 0;
                        |};
                      |};
                      cr_ctx := BCEmp;
                      cr_rel := btrue;
                   |} q1 q2 ->
  pre_bisimulation A
                   (wp_one r_states)
                   top
                   []
                   (mk_init _ _ _ BabyIP.aut 10 BabyIP1.Start BabyIP2.Start)
                   q1 q2.
Proof.
  idtac "running babyip bisimulation".

  intros.
  set (rel0 := (mk_init _ _ _ BabyIP.aut 10 BabyIP1.Start BabyIP2.Start)).
  vm_compute in rel0.
  subst rel0.

  time "single step" run_bisim top top' r_states.
  verify_interp top top'.

  time "build phase" repeat (time "single step" run_bisim top top' r_states).
  time "close phase" close_bisim' top top' r_states_conv.
Time Admitted.
