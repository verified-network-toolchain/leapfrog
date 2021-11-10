Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.DataCenter.

Require Import Coq.Arith.PeanoNat.


Declare ML Module "mirrorsolve".

Notation H := (DataCenter.header + DataCenter.header).
Notation A := (Sum.sum DataCenter.aut DataCenter.aut).
Notation conf := (P4automaton.configuration (P4A.interp A)).
Notation start_left := (DataCenter.ParseEth0).
Notation start_right := (DataCenter.ParseEth0).

SetSMTSolver "cvc4".

Notation r_len := 10.
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

(* ClearEnvCtors. *)

(* | HdrEth0: header eth_size
| HdrEth1: header eth_size
| HdrVLAN0: header vlan_size
| HdrVLAN1: header vlan_size
| HdrIPv4: header ipv4_size
| HdrTCP: header tcp_size
| HdrUDP: header udp_size
| HdrGRE0: header gre_size
| HdrGRE1: header gre_size
| HdrGRE2: header gre_size
| HdrNVGRE: header nv_gre_size
| HdrVXLAN: header vxlan_size *)

(* 
RegisterEnvCtors
  (HdrEth0, FirstOrderConfRelSimplified.Bits eth_size)
  (HdrEth1, FirstOrderConfRelSimplified.Bits eth_size)
  (HdrVLAN0, FirstOrderConfRelSimplified.Bits vlan_size)
  (HdrVLAN1, FirstOrderConfRelSimplified.Bits vlan_size)
  (HdrGRE0, FirstOrderConfRelSimplified.Bits gre_size)
  (HdrGRE1, FirstOrderConfRelSimplified.Bits gre_size)
  (HdrGRE2, FirstOrderConfRelSimplified.Bits gre_size)
  (HdrIPv4, FirstOrderConfRelSimplified.Bits ipv4_size)
  (HdrTCP, FirstOrderConfRelSimplified.Bits tcp_size)
  (HdrUDP, FirstOrderConfRelSimplified.Bits udp_size)
  (HdrNVGRE, FirstOrderConfRelSimplified.Bits nv_gre_size)
  (HdrVXLAN, FirstOrderConfRelSimplified.Bits vxlan_size). *)



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
  idtac "running datacenter self-comparison bisimulation".

  intros.
  set (rel0 := (mk_init _ _ _ _ _ _ _)).
  vm_compute in rel0.
  subst rel0.

  time "build phase" repeat (time "single step" run_bisim top top' r_states).

  (* run_bisim top top' r_states. *)
  time "close phase" close_bisim top'.
Time Admitted.
