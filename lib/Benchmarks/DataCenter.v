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

Notation eth_size := 112.
Notation vlan_size := 160.
Notation ipv4_size := 160.
Notation icmp_size := 32.
Notation tcp_size := 160.
Notation udp_size := 160.
Notation gre_size := 32.
Notation nv_gre_size := 32.
Notation vxlan_size := 64.
Notation arp_size := 64.

Inductive header: nat -> Type :=
| HdrEth0: header eth_size
| HdrEth1: header eth_size
| HdrVLAN0: header vlan_size
| HdrVLAN1: header vlan_size
| HdrIPv4: header ipv4_size
| HdrICMP: header icmp_size
| HdrTCP: header tcp_size
| HdrUDP: header udp_size
| HdrGRE0: header gre_size
| HdrGRE1: header gre_size
| HdrGRE2: header gre_size
| HdrNVGRE: header nv_gre_size
| HdrVXLAN: header vxlan_size
| HdrARP: header arp_size
| HdrARPIP: header ipv4_size.

Derive Signature for header.
Definition h112_eq_dec (x y: header 112) : {x = y} + {x <> y}.
refine (
  match x with
  | HdrEth0 =>
    match y with
    | HdrEth0 => left eq_refl
    | HdrEth1 => right _
    end
  | HdrEth1 =>
    match y with
    | HdrEth0 => right _
    | HdrEth1 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h32_eq_dec (x y: header 32) : {x = y} + {x <> y}.
refine (
  match x with
  | HdrICMP =>
    match y with
    | HdrICMP => left eq_refl
    | HdrGRE0 => right _
    | HdrGRE1 => right _
    | HdrGRE2 => right _
    | HdrNVGRE => right _
    end
  | HdrGRE0 =>
    match y with
    | HdrICMP => right _
    | HdrGRE0 => left eq_refl
    | HdrGRE1 => right _
    | HdrGRE2 => right _
    | HdrNVGRE => right _
    end
  | HdrGRE1 =>
    match y with
    | HdrICMP => right _
    | HdrGRE0 => right _
    | HdrGRE1 => left eq_refl
    | HdrGRE2 => right _
    | HdrNVGRE => right _
    end
  | HdrGRE2 =>
    match y with
    | HdrICMP => right _
    | HdrGRE0 => right _
    | HdrGRE1 => right _
    | HdrGRE2 => left eq_refl
    | HdrNVGRE => right _
    end
  | HdrNVGRE =>
    match y with
    | HdrICMP => right _
    | HdrGRE0 => right _
    | HdrGRE1 => right _
    | HdrGRE2 => right _
    | HdrNVGRE => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h64_eq_dec (x y: header 64) : {x = y} + {x <> y}.
refine (
  match x with
  | HdrVXLAN =>
    match y with
    | HdrVXLAN => left eq_refl
    | HdrARP => right _
    end
  | HdrARP =>
    match y with
    | HdrARP => left eq_refl
    | HdrVXLAN => right _
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h160_eq_dec (x y: header 160) : {x = y} + {x <> y}.
refine (
  match x with
  | HdrVLAN0 =>
    match y with
    | HdrVLAN0 => left eq_refl
    | HdrVLAN1 => right _
    | HdrIPv4 => right _
    | HdrTCP => right _
    | HdrUDP => right _
    | HdrARPIP => right _
    end
  | HdrVLAN1 =>
    match y with
    | HdrVLAN0 => right _
    | HdrVLAN1 => left eq_refl
    | HdrIPv4 => right _
    | HdrTCP => right _
    | HdrUDP => right _
    | HdrARPIP => right _
    end
  | HdrIPv4 =>
    match y with
    | HdrVLAN0 => right _
    | HdrVLAN1 => right _
    | HdrIPv4 => left eq_refl
    | HdrTCP => right _
    | HdrUDP => right _
    | HdrARPIP => right _
    end
  | HdrTCP =>
    match y with
    | HdrVLAN0 => right _
    | HdrVLAN1 => right _
    | HdrIPv4 => right _
    | HdrTCP => left eq_refl
    | HdrUDP => right _
    | HdrARPIP => right _
    end
  | HdrUDP =>
    match y with
    | HdrVLAN0 => right _
    | HdrVLAN1 => right _
    | HdrIPv4 => right _
    | HdrTCP => right _
    | HdrUDP => left eq_refl
    | HdrARPIP => right _
    end
  | HdrARPIP =>
    match y with
    | HdrVLAN0 => right _
    | HdrVLAN1 => right _
    | HdrIPv4 => right _
    | HdrTCP => right _
    | HdrUDP => right _
    | HdrARPIP => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
  solve_header_eqdec_ n x y
    ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h112_eq_dec) ::
     (existT _ _ h32_eq_dec) ::
     (existT _ _ h64_eq_dec) ::
     (existT _ _ h160_eq_dec) ::
      nil).
Defined.

Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.
Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  solve_eqdec'.
Defined.
Global Instance header_finite: forall n, @Finite (header n) _ _.
  intros n; solve_indexed_finiteness n [112; 32 ; 64 ; 160 ].
Qed.

Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
  {| enum := [
      existT _ _ HdrEth0
    ; existT _ _ HdrEth1
    ; existT _ _ HdrVLAN0
    ; existT _ _ HdrVLAN1
    ; existT _ _ HdrICMP
    ; existT _ _ HdrIPv4
    ; existT _ _ HdrTCP
    ; existT _ _ HdrUDP
    ; existT _ _ HdrGRE0
    ; existT _ _ HdrGRE1
    ; existT _ _ HdrGRE2
    ; existT _ _ HdrNVGRE
    ; existT _ _ HdrVXLAN
    ; existT _ _ HdrARP
    ; existT _ _ HdrARPIP
    ] |}.
Next Obligation.
  solve_header_finite.
Qed.
Next Obligation.
dependent destruction X; subst;
repeat (
  match goal with
  | |- ?L \/ ?R => (now left; trivial) || right
  end
).
Qed.

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

Scheme Equality for state.
Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
Global Program Instance state_finite: @Finite state _ state_eq_dec :=
  {| enum := [ParseEth0; ParseEth1; ParseVLAN0; ParseVLAN1; ParseICMP; ParseIPv4; ParseTCP; ParseUDP; ParseGRE0; ParseGRE1; ParseGRE2; ParseNVGRE; ParseVXLAN; ParseARP; ParseARPIP] |}.
Next Obligation.
repeat constructor;
  repeat match goal with
          | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
          | |- ~ List.In _ [] => apply List.in_nil
          | |- ~ List.In _ (_ :: _) => unfold not; intros
          | H: List.In _ (_::_) |- _ => inversion H; clear H
          | _ => discriminate
          end.
Qed.
Next Obligation.
  destruct x; intuition congruence.
Qed.

Program Definition aut: Syntax.t state header :=
  {| t_states := states |}.
Solve Obligations with (destruct s; vm_compute; Lia.lia).
