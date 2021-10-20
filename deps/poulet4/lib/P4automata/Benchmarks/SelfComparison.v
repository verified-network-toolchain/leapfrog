Require Coq.Classes.EquivDec.
Require Import Coq.Arith.PeanoNat.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.P4automata.Notations.

Open Scope p4a.

(*
This example is an undefined-value example inspired by the running
example in the SafeP4 paper (https://arxiv.org/pdf/1906.07223.pdf).
*)

Module ReadUndef.
  Inductive state :=
  | ParseEth
  | DefaultVLAN
  | ParseVLAN
  | ParseIP
  | ParseUDP.
  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Qed.

  (* These sizes should be bigger. *)
  Notation eth_size := 2.
  Notation ip_size := 2.
  Notation vlan_size := 2.
  Notation udp_size := 2.
  Inductive header : nat -> Type :=
  | HdrEth: header eth_size
  | HdrIP: header ip_size
  | HdrVLAN: header vlan_size
  | HdrUDP: header udp_size.

  Equations header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y} :=
  {
    header_eqdec_ _ HdrEth HdrEth := left eq_refl ;
    header_eqdec_ _ HdrIP HdrIP := left eq_refl ;
    header_eqdec_ _ HdrVLAN HdrVLAN := left eq_refl ;
    header_eqdec_ _ HdrUDP HdrUDP := left eq_refl ;
    header_eqdec_ _ _ _ := ltac:(right; congruence) ;
  }.
  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (H' header) eq.
  Proof.
    solve_eqdec'.
  Qed.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [2; 2; 2; 2].
  Qed.
  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ HdrEth ;
                 existT _ _ HdrIP ;
                 existT _ _ HdrVLAN ;
                 existT _ _ HdrUDP ] |}.
  Next Obligation.
    repeat constructor;
    unfold "~";
    intros;
    cbn in *;
    repeat match goal with
           | H: False |- False => exact H
           | H: _ = _ |- _ => inversion H
           | H: _ \/ _ |- _ => destruct H
           end.
  Qed.
  Next Obligation.
  dependent destruction X; subst;
  repeat (
    match goal with
    | |- ?L \/ ?R => (now left; trivial) || right
    end
  ).
  Qed.

  Definition states (s: state) : P4A.state state header :=
    match s with
    | ParseEth =>
      {| st_op := extract(HdrEth);
         st_trans := transition select (| (EHdr HdrEth)[0 -- 0] |) {{
                                    [| exact #b|0 |] ==> inl DefaultVLAN ;;;
                                    [| exact #b|1 |] ==> inl ParseVLAN ;;;
                                    reject
                                }}
      |}
    | DefaultVLAN =>
      {| st_op := HdrVLAN <- ELit (Ntuple.l2t (cons 0 (cons 0 nil))%p4abits);;
                  extract(HdrIP);
         st_trans := transition (inl ParseUDP)
      |}
    | ParseIP =>
      {| st_op := extract(HdrIP);
         st_trans := transition (inl ParseUDP)
      |}
    | ParseVLAN =>
      {| st_op := extract(HdrVLAN);
         st_trans := transition (inl ParseIP)
      |}
    | ParseUDP =>
      {| st_op := extract(HdrUDP);
         st_trans := transition select (| EHdr HdrVLAN |) {{
                                    [| exact #b|1|1 |] ==> reject ;;;
                                    accept
                                }}
      |}
    end.

  Program Definition aut: Syntax.t state _ :=
    {| t_states := states |}.
  Next Obligation.
    destruct s; cbv.
    cbv.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End ReadUndef.
