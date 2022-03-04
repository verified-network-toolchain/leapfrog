Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.

Require Import Leapfrog.Syntax.
Require Import Leapfrog.FinType.
Require Import Leapfrog.Sum.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.Notations.

Require Import Leapfrog.BisimChecker.
Require Import Coq.Program.Equality.

Open Scope p4a.

Module Simple.

  Notation eth_size := 112.
  Notation vlan_size := 160.
  Notation ipv4_size := 64.
  Notation ipv6_size := 64.
  Notation icmp_size := 32.
  Notation tcp_size := 160.
  Notation udp_size := 160.
  Notation arp_size := 64.

  Inductive header :=
  | HdrEth
  | HdrVLAN0
  | HdrVLAN1
  | HdrIPv4
  | HdrIPv6
  | HdrTCP
  | HdrUDP
  | HdrICMP
  | HdrICMPv6
  | HdrARP
  | HdrARPIP.

  Definition sz (h: header) : nat :=
    match h with
    | HdrEth => 112
    | HdrVLAN0
    | HdrVLAN1 => 160
    | HdrIPv4 => 64
    | HdrIPv6 => 64
    | HdrTCP => 160
    | HdrUDP => 160
    | HdrICMP => 32
    | HdrICMPv6 => 32
    | HdrARP => 64
    | HdrARPIP => 64
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive state: Type :=
  | ParseEth
  | ParseVLAN0
  | ParseVLAN1
  | ParseIPv4
  | ParseIPv6
  | ParseTCP
  | ParseUDP
  | ParseICMP
  | ParseICMPv6
  | ParseARP
  | ParseARPIP.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) : P4A.state state sz :=
    match s with
    | ParseEth =>
      {| st_op := extract(HdrEth);
        st_trans := transition select (| (EHdr HdrEth)[111--96] |)
                                {{ [| hexact 0x8100 |] ==> inl ParseVLAN0 ;;;
                                  [| hexact 0x9100 |] ==> inl ParseVLAN0 ;;;
                                  [| hexact 0x9200 |] ==> inl ParseVLAN0 ;;;
                                  [| hexact 0x9300 |] ==> inl ParseVLAN0 ;;;
                                  [| hexact 0x0800 |] ==> inl ParseIPv4 ;;;
                                  [| hexact 0x86dd |] ==> inl ParseIPv6 ;;;
                                  [| hexact 0x0806 |] ==> inl ParseARP ;;;
                                  [| hexact 0x8035 |] ==> inl ParseARP ;;;
                                  reject }}
      |}
    | ParseVLAN0 =>
      {| st_op := extract(HdrVLAN0) ;
        st_trans := transition select (| (EHdr HdrVLAN0)[159--144] |)
                                {{ [| hexact 0x8100 |] ==> inl ParseVLAN1 ;;;
                                  [| hexact 0x9100 |] ==> inl ParseVLAN1 ;;;
                                  [| hexact 0x9200 |] ==> inl ParseVLAN1 ;;;
                                  [| hexact 0x9300 |] ==> inl ParseVLAN1 ;;;
                                  [| hexact 0x0800 |] ==> inl ParseIPv4 ;;;
                                  [| hexact 0x86dd |] ==> inl ParseIPv6 ;;;
                                  [| hexact 0x0806 |] ==> inl ParseARP ;;;
                                  [| hexact 0x8035 |] ==> inl ParseARP ;;;
                                  reject }}
      |}
    | ParseVLAN1 =>
      {| st_op := extract(HdrVLAN1) ;
        st_trans := transition select (| (EHdr HdrVLAN1)[159--144] |)
                                {{ [| hexact 0x0800 |] ==> inl ParseIPv4 ;;;
                                  [| hexact 0x86dd |] ==> inl ParseIPv6 ;;;
                                  [| hexact 0x0806 |] ==> inl ParseARP ;;;
                                  [| hexact 0x8035 |] ==> inl ParseARP ;;;
                                  reject }}
      |}
    | ParseIPv4 =>
      {| st_op := extract(HdrIPv4);
        st_trans := transition select (| (EHdr HdrIPv4)[79--72] |)
                                {{ [| hexact 1 |] ==> inl ParseICMP;;;
                                  [| hexact 6 |] ==> inl ParseTCP;;;
                                  [| hexact 17 |] ==> inl ParseUDP;;;
                                  accept
                                }}
      |}
    | ParseIPv6 =>
      {| st_op := extract(HdrIPv6);
        st_trans := transition select (| (EHdr HdrIPv6)[55--48] |)
                                {{ [| hexact 1 |] ==> inl ParseICMPv6;;;
                                  [| hexact 6 |] ==> inl ParseTCP;;;
                                  [| hexact 17 |] ==> inl ParseUDP;;;
                                  accept
                                }}
      |}
    | ParseUDP =>
      {| st_op := extract(HdrUDP);
        st_trans := transition accept |}
    | ParseTCP =>
      {| st_op := extract(HdrTCP);
        st_trans := transition accept |}
    | ParseICMP =>
      {| st_op := extract(HdrICMP);
        st_trans := transition accept |}
    | ParseICMPv6 =>
      {| st_op := extract(HdrICMPv6);
        st_trans := transition accept |}
    | ParseARP =>
      {| st_op := extract(HdrARP);
        st_trans := transition select (| (EHdr HdrARP)[31--16] |)
                                {{ [| hexact 0x0800 |] ==> inl ParseARPIP;;;
                                  accept
                                }}
      |}
    | ParseARPIP =>
      {| st_op := extract(HdrARPIP);
        st_trans := transition accept
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).
End Simple.
