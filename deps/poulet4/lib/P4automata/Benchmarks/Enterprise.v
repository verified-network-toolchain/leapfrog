Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.

Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.P4automata.Notations.

Open Scope p4a.

Notation eth_size := 112.
Notation vlan_size := 160.
Notation ipv4_size := 64.
Notation ipv6_size := 64.
Notation tcp_size := 160.
Notation udp_size := 160.
Notation icmp_size := 32.

Inductive header: nat -> Type :=
| HdrEth: header eth_size
| HdrVLAN0: header vlan_size
| HdrVLAN1: header vlan_size
| HdrIPv4: header ipv4_size
| HdrIPv6: header ipv6_size
| HdrTCP: header tcp_size
| HdrUDP: header udp_size
| HdrICMP: header icmp_size.

Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
Proof.
Admitted.
Global Instance header_finite: forall n, @Finite (header n) _ _.
Proof.
Admitted.
Global Instance header_finite': @Finite {n & header n} _ header_eqdec'.
Admitted.

Inductive state: Type :=
| ParseEth
| ParseVLAN0
| ParseVLAN1
| ParseIPv4
| ParseIPv6
| ParseTCP
| ParseUDP
| ParseICMP.

Definition states (s: state) : P4A.state state header :=
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
                                 reject }}
    |}
  | ParseVLAN1 =>
    {| st_op := extract(HdrVLAN1) ;
       st_trans := transition select (| (EHdr HdrVLAN1)[159--144] |)
                              {{ [| hexact 0x0800 |] ==> inl ParseIPv4 ;;;
                                 [| hexact 0x86dd |] ==> inl ParseIPv6 ;;;
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
                              {{ [| hexact 1 |] ==> inl ParseICMP;;;
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
  end.
