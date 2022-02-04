Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.TCAMSimple.


Notation H := (VerySimple.header + Optimized.header).
Notation A := (Sum.sum VerySimple.aut Optimized.aut).
Notation conf := (P4automaton.configuration (P4A.interp A)).
Notation start_left := VerySimple.Ethernet.
Notation start_right := Optimized.State_0.

Require Import Coq.Arith.PeanoNat.

Fixpoint reachable_states_len' (r: Reachability.state_pairs A) (fuel: nat) :=
  match fuel with
  | 0 => None
  | S x =>
    let nxt := Reachability.reachable_step r in
    let nxt_len := length nxt in
    if Nat.eq_dec (length nxt) (length r) then Some nxt_len
    else
      reachable_states_len' nxt x
  end.

Definition reachable_states_len : nat.
  refine (
  let s := ({| st_state := inl (inl start_left); st_buf_len := 0 |},
            {| st_state := inl (inr start_right); st_buf_len := 0 |}) in
  let r := reachable_states_len' [s] 1000 in
  _).
  vm_compute in r.
  match goal with
  | _ := Some ?x |- _ => exact x
  end.
  Defined.

Definition r_states :=
  Eval vm_compute in (Reachability.reachable_states
                        A
                        reachable_states_len
                        start_left
                        start_right).

Definition top : Relations.rel conf :=
  fun q1 q2 => List.In (conf_to_state_template q1, conf_to_state_template q2) r_states.

Definition top' : Relations.rel (state_template A) :=
  fun q1 q2 => List.In (q1, q2) r_states.

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
                   (mk_init _ _ _ A reachable_states_len start_left start_right)
                   q1 q2.
Proof.
  idtac "running tcam very simple bisimulation".

  intros.
  set (rel0 := (mk_init _ _ _ _ _ _ _)).
  vm_compute in rel0.
  subst rel0.



  time "build phase" repeat (time "single step" run_bisim top top' r_states).

  time "close phase" close_bisim top'.

Time Admitted.
