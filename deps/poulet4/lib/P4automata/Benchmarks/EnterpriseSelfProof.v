Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.Enterprise.

Require Import Coq.Arith.PeanoNat.


Declare ML Module "mirrorsolve".

Notation H := (Simple.header + Simple.header).
Notation A := (Sum.sum Simple.aut Simple.aut).
Notation conf := (P4automaton.configuration (P4A.interp A)).
Notation start_left := (Simple.ParseEth).
Notation start_right := (Simple.ParseEth).

Notation r_len := 4.

Definition r_states : list (Reachability.state_pair A) :=
  Eval vm_compute in (Reachability.reachable_states
                        A
                        r_len
                        start_left
                        start_right).



(* Definition r_states' :=
  Eval vm_compute in (Reachability.reachable_step r_states).

Definition r_len := Eval vm_compute in (length r_states, length r_states').

Print r_len. *)

Definition top : Relations.rel conf := fun _ _ => True.
Definition top' : Relations.rel (state_template A) := fun _ _ => True.

ClearEnvCtors.

(* | HdrEth: header eth_size
| HdrVLAN0: header vlan_size
| HdrVLAN1: header vlan_size
| HdrIPv4: header ipv4_size
| HdrIPv6: header ipv6_size
| HdrTCP: header tcp_size
| HdrUDP: header udp_size
| HdrICMP *)

(*
RegisterEnvCtors
  (Enterprise.HdrEth, FirstOrderConfRelSimplified.Bits eth_size)
  (Enterprise.HdrVLAN0, FirstOrderConfRelSimplified.Bits vlan_size)
  (Enterprise.HdrVLAN1, FirstOrderConfRelSimplified.Bits vlan_size)
  (Enterprise.HdrIPv4, FirstOrderConfRelSimplified.Bits ipv4_size)
  (Enterprise.HdrIPv6, FirstOrderConfRelSimplified.Bits ipv6_size)
  (Enterprise.HdrTCP, FirstOrderConfRelSimplified.Bits tcp_size)
  (Enterprise.HdrUDP, FirstOrderConfRelSimplified.Bits udp_size)
  (Enterprise.HdrICMP, FirstOrderConfRelSimplified.Bits icmp_size).
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
                  (mk_init _ _ _ _ A r_len start_left start_right)
                  q1 q2.
Proof.
  idtac "running enterprise self-comparison bisimulation".

  intros.
  set (rel0 := (mk_init _ _ _ _ _ _ _ _)).
  vm_compute in rel0.
  subst rel0.

  time "build phase" repeat (time "single step" run_bisim top top' r_states).

  (* run_bisim top top' r_states. *)
  time "close phase" close_bisim top'.
Time Admitted.
