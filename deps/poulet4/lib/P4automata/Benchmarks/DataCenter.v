Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.

Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.P4automata.Notations.

Require Import Poulet4.P4automata.BisimChecker.
Require Import Coq.Program.Equality.

Open Scope p4a.

Inductive header :=
| HdrEth0
| HdrEth1
| HdrVLAN0
| HdrVLAN1
| HdrIPv4
| HdrICMP
| HdrTCP
| HdrUDP
| HdrGRE0
| HdrGRE1
| HdrGRE2
| HdrNVGRE
| HdrVXLAN
| HdrARP
| HdrARPIP.

Definition sz (h: header) : nat :=
  match h with
  | HdrEth0
  | HdrEth1 => 112
  | HdrVLAN0
  | HdrVLAN1 => 160
  | HdrIPv4 => 160
  | HdrICMP => 32
  | HdrTCP => 160
  | HdrUDP => 160
  | HdrGRE0
  | HdrGRE1
  | HdrGRE2 => 32
  | HdrNVGRE => 32
  | HdrVXLAN => 64
  | HdrARP => 64
  | HDRARPIP => 160
  end.

Scheme Equality for header.
Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
Global Instance header_finite: @Finite header _ header_eq_dec.
Proof.
  solve_finiteness.
Defined.

Inductive state: Type :=
| ParseEth0 (* start state *)
| ParseEth1
| ParseVLAN0
| ParseVLAN1
| ParseICMP
| ParseIPv4
| ParseTCP
| ParseUDP
| ParseGRE0
| ParseGRE1
| ParseGRE2
| ParseNVGRE
| ParseVXLAN
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
  | ParseEth0 =>
    {| st_op := extract(HdrEth0);
       st_trans := transition select (| (EHdr HdrEth0)[111--96] |)
                              {{ [| hexact 0x8100 |] ==> inl ParseVLAN0 ;;;
                                 [| hexact 0x9100 |] ==> inl ParseVLAN0 ;;;
                                 [| hexact 0x9200 |] ==> inl ParseVLAN0 ;;;
                                 [| hexact 0x9300 |] ==> inl ParseVLAN0 ;;;
                                 [| hexact 0x0800 |] ==> inl ParseIPv4 ;;;
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
                                 [| hexact 0x0806 |] ==> inl ParseARP ;;;
                                 [| hexact 0x8035 |] ==> inl ParseARP ;;;
                                 reject }}
    |}
  | ParseVLAN1 =>
    {| st_op := extract(HdrVLAN1) ;
       st_trans := transition select (| (EHdr HdrVLAN1)[159--144] |)
                              {{ [| hexact 0x0800 |] ==> inl ParseIPv4 ;;;
                                 [| hexact 0x0806 |] ==> inl ParseARP ;;;
                                 [| hexact 0x8035 |] ==> inl ParseARP ;;;
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
  | ParseICMP =>
    {| st_op := extract(HdrICMP);
       st_trans := transition accept |}
  | ParseTCP =>
    {| st_op := extract(HdrTCP);
       st_trans := transition accept |}
  | ParseGRE0 =>
    {| st_op := extract(HdrGRE0);
       st_trans := transition select (| (EHdr HdrGRE0)[2--2], (EHdr HdrGRE0)[31--16] |)
                              {{ [| hexact 0x1, hexact 0x6558 |] ==> inl ParseNVGRE;;;
                                 [| hexact 0x1, hexact 0x6559 |] ==> inl ParseGRE1;;;
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
Solve Obligations with (destruct s || destruct h; vm_compute; Lia.lia).
