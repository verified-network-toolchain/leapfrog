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
Notation mpls_size := 32.
Notation eompls_size := 32.
Notation ipv4_size := 156.
Notation ipv6_size := 316.

Inductive header: nat -> Type :=
| HdrEth0: header eth_size
| HdrEth1: header eth_size
| HdrMPLS0: header mpls_size
| HdrMPLS1: header mpls_size
| HdrEoMPLS: header eompls_size
| HdrIPVer: header 4
| HdrIPv4: header ipv4_size
| HdrIPv6: header ipv6_size.

Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
Proof.
Admitted.
Global Instance header_finite: forall n, @Finite (header n) _ _.
Proof.
Admitted.
Global Instance header_finite': @Finite {n & header n} _ header_eqdec'.
Admitted.

Inductive state: Type :=
| ParseEth0
| ParseEth1
| ParseMPLS0
| ParseMPLS1
| ParseEoMPLS
| ParseIPVer
| ParseIPv4
| ParseIPv6.

Definition states (s: state) : P4A.state state header :=
  match s with
  | ParseEth0 =>
    {| st_op := extract(HdrEth0);
       st_trans := transition select (| (EHdr HdrEth0)[111--96] |)
                              {{ [| hexact 0x8847 |] ==> inl ParseMPLS0 ;;;
                                 [| hexact 0x8848 |] ==> inl ParseMPLS0 ;;;
                                 [| hexact 0x0800 |] ==> inl ParseIPv4 ;;;
                                 [| hexact 0x86dd |] ==> inl ParseIPv6 ;;;
                                 reject }}
    |}
  | ParseMPLS0 => 
    {| st_op := extract(HdrMPLS0);
       st_trans := transition select (| (EHdr HdrMPLS0)[24--24] |)
                              {{ [| hexact 0 |] ==> inl ParseMPLS1 ;;;
                                 [| hexact 1 |] ==> inl ParseIPVer ;;;
                                 reject
                              }}
    |}
  | ParseMPLS1 => 
    {| st_op := extract(HdrMPLS1);
       st_trans := transition (inl ParseIPVer)
    |}
  | ParseIPVer =>
    {| st_op := extract(HdrIPVer);
       st_trans := transition select (| EHdr HdrIPVer |)
                              {{ [| exact #b|0|0|0|0 |] ==> inl ParseEoMPLS;;;
                                 [| exact #b|0|1|0|0 |] ==> inl ParseIPv4;;;
                                 [| exact #b|0|1|1|0 |] ==> inl ParseIPv6;;;
                                 reject
                              }}
    |}
  | ParseEoMPLS =>
    {| st_op := extract(HdrEoMPLS);
       st_trans := transition (inl ParseEth1) |}
  | ParseIPv4 =>
    {| st_op := extract(HdrIPv4);
       st_trans := transition accept |}
  | ParseIPv6 =>
    {| st_op := extract(HdrIPv6);
       st_trans := transition accept |}
  | ParseEth1 =>
    {| st_op := extract(HdrEth1);
       st_trans := transition accept |}
  end.



