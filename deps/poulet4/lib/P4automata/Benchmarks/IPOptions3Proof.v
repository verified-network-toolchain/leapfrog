Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.IPOptions.
Require Import Poulet4.P4automata.Benchmarks.Timestamp.

Require Import Coq.Arith.PeanoNat.

Notation H := (IPOptionsRef63.header + TimestampSpec3.header).
Notation A := (Sum.sum IPOptionsRef63.aut TimestampSpec3.aut).
Notation conf := (P4automaton.configuration (P4A.interp A)).
Notation start_left := IPOptionsRef63.Parse0.
Notation start_right := TimestampSpec3.Parse0.


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

Definition r_len : nat.
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
                        r_len
                        start_left
                        start_right).


Definition top : Relations.rel conf := fun _ _ => True.
Definition top' : Relations.rel (state_template A) := fun _ _ => True.

Declare ML Module "mirrorsolve".

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
                   (mk_init _ _ _ _ A r_len start_left start_right)
                   q1 q2.
Proof.
  idtac "running timestamp three bisimulation".

  intros.
  set (a := A).
  set (rel0 := (mk_init _ _ _ _ _ _ _ _)).
  vm_compute in rel0.

  time "build phase" repeat (run_bisim top top' r_states).
  time "close phase" close_bisim top'.

Time Admitted.
