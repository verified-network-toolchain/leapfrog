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

Notation eth_size := 112.
Notation vlan_size := 160.
Notation ipv4_size := 64.
Notation tcp_size := 160.
Notation udp_size := 160.
Notation gre_size := 32.
Notation nv_gre_size := 32.
Notation vxlan_size := 64.

Inductive header: nat -> Type :=
| HdrEth0: header eth_size
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
| HdrVXLAN: header vxlan_size.

Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
Proof.
Admitted.
Global Instance header_finite: forall n, @Finite (header n) _ _.
Proof.
Admitted.
Global Instance header_finite': @Finite {n & header n} _ header_eqdec'.
Admitted.  

Inductive state: Type :=
| ParseEth0 (* start state *)
| ParseEth1
| ParseVLAN0
| ParseVLAN1
| ParseIPv4
| ParseTCP
| ParseUDP
| ParseGRE0
| ParseGRE1
| ParseGRE2
| ParseNVGRE
| ParseVXLAN.

Check 0x1000.


Definition states (s: state) : P4A.state state header :=
  match s with
  | ParseEth0 =>
    {| st_op := extract(HdrEth0);
       st_trans := transition select (| (EHdr HdrEth0)[111--96] |)
                              {{ [| hexact 0x8100 |] ==> inl ParseVLAN0 ;;;
                                 [| hexact 0x9100 |] ==> inl ParseVLAN0 ;;;
                                 [| hexact 0x9200 |] ==> inl ParseVLAN0 ;;;
                                 [| hexact 0x9300 |] ==> inl ParseVLAN0 ;;;
                                 [| hexact 0x0800 |] ==> inl ParseIPv4 ;;;
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
                                 reject }}
    |}
  | ParseVLAN1 =>
    {| st_op := extract(HdrVLAN1) ;
       st_trans := transition select (| (EHdr HdrVLAN1)[159--144] |)
                              {{ [| hexact 0x0800 |] ==> inl ParseIPv4 ;;;
                                 reject }}
    |}
  | ParseIPv4 =>
    {| st_op := extract(HdrIPv4);
       st_trans := transition select (| (EHdr HdrIPv4)[79--72] |)
                              {{ [| hexact 6 |] ==> inl ParseTCP;;;
                                 [| hexact 17 |] ==> inl ParseUDP;;;
                                 [| hexact 47 |] ==> inl ParseGRE0;;;
                                 accept
                              }}
    |}
  | ParseUDP =>
    {| st_op := extract(HdrUDP);
       st_trans := transition select (| (EHdr HdrUDP)[31--16] |)
                              {{ [| hexact 0xFFFF |] ==> inl ParseVXLAN;;;
                                 accept
                              }}
    |}
  | ParseTCP =>
    {| st_op := extract(HdrTCP);
       st_trans := transition accept |}
  | ParseGRE0 =>
    {| st_op := extract(HdrGRE0);
       st_trans := transition select (| (EHdr HdrGRE0)[31--16] |)
                              {{ [| hexact 0x16558 |] ==> inl ParseNVGRE;;;
                                 [| hexact 0x16559 |] ==> inl ParseGRE1;;;
                                 accept
                              }}
    |}
  | ParseGRE1 =>
    {| st_op := extract(HdrGRE1);
       st_trans := transition select (| (EHdr HdrGRE1)[31--16] |)
                              {{ [| hexact 0x16558 |] ==> inl ParseNVGRE;;;
                                 [| hexact 0x16559 |] ==> inl ParseGRE2;;;
                                 accept
                              }}
    |}
  | ParseGRE2 =>
    {| st_op := extract(HdrGRE2);
       st_trans := transition select (| (EHdr HdrGRE2)[31--16] |)
                              {{ [| hexact 0x16558 |] ==> inl ParseNVGRE;;;
                                 [| hexact 0x16559 |] ==> reject;;;
                                 accept
                              }}
    |}
  | ParseNVGRE =>
    {| st_op := extract(HdrNVGRE);
       st_trans := transition (inl ParseEth1) |}
  | ParseVXLAN =>
    {| st_op := extract(HdrVXLAN);
       st_trans := transition (inl ParseEth1) |}
  | ParseEth1 =>
    {| st_op := extract(HdrEth1);
       st_trans := transition accept |}
  end.

