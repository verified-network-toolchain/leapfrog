Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.Edge.

Require Import Coq.Arith.PeanoNat.


Declare ML Module "mirrorsolve".

Notation H := (Edge.header + Edge.header).
Notation A := (Sum.sum Edge.aut Edge.aut).
Notation conf := (P4automaton.configuration (P4A.interp A)).
Notation start_left := (Edge.ParseEth0).
Notation start_right := (Edge.ParseEth0).

Notation r_len := 7.
(* Fixpoint reachable_states_len' (r: Reachability.state_pairs A) (acc: nat) (fuel: nat) :=
  match fuel with
  | 0 => None
  | S x =>
    let nxt := Reachability.reachable_step r in
    let nxt_len := length nxt in
    if Nat.eq_dec (length nxt) (length r) then Some acc
    else
      reachable_states_len' nxt (S acc) x
  end.

Definition reachable_states_len : nat.
  refine (
  let s := ({| st_state := inl (inl start_left); st_buf_len := 0 |},
            {| st_state := inl (inr start_right); st_buf_len := 0 |}) in
  let r := reachable_states_len' [s] 0 1000 in
  _).
  vm_compute in r.
  match goal with
  | _ := Some ?x |- _ => exact x
  end.
  Defined.
Print reachable_states_len. *)
Definition r_states : list (Reachability.state_pair A) :=
  Eval vm_compute in (Reachability.reachable_states
                        A
                        r_len
                        start_left
                        start_right).

Definition top : Relations.rel conf := fun _ _ => True.
Definition top' : Relations.rel (state_template A) := fun _ _ => True.

ClearEnvCtors.

(* | HdrEth0: header eth_size
| HdrEth1: header eth_size
| HdrMPLS0: header mpls_size
| HdrMPLS1: header mpls_size
| HdrEoMPLS: header eompls_size
| HdrIPVer: header 4
| HdrIPv4: header ipv4_size
| HdrIPv6: header ipv6_size *)

(*
RegisterEnvCtors
  (HdrEth0, FirstOrderConfRelSimplified.Bits eth_size)
  (HdrEth1, FirstOrderConfRelSimplified.Bits eth_size)
  (HdrMPLS0, FirstOrderConfRelSimplified.Bits mpls_size)
  (HdrMPLS1, FirstOrderConfRelSimplified.Bits mpls_size)
  (HdrEoMPLS, FirstOrderConfRelSimplified.Bits eompls_size)
  (HdrIPVer, FirstOrderConfRelSimplified.Bits 4)
  (HdrIPv4, FirstOrderConfRelSimplified.Bits ipv4_size)
  (HdrIPv6, FirstOrderConfRelSimplified.Bits ipv4_size).
*)

Lemma prebisim_babyip:
  forall q1 q2,
    interp_conf_rel' {| cr_st := {|
                        cs_st1 := {|
                          st_state := inl (inl start_left);
                          st_buf_len := 0;
                        |};
                        cs_st2 := {|
                          st_state := inl (inr start_right);
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
                  (mk_init _ _ _ A r_len start_left start_right)
                  q1 q2.
Proof.
  idtac "running edge self-comparison bisimulation".

  intros.
  set (rel0 := (mk_init _ _ _ _ _ _ _)).
  vm_compute in rel0.
  subst rel0.

  time "build phase" repeat (time "single step" run_bisim top top' r_states).

  (* run_bisim top top' r_states. *)
  time "close phase" close_bisim top'.
Time Admitted.
