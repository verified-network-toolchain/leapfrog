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

Derive Signature for header.
Definition h112_eq_dec (x y: header 112) : {x = y} + {x <> y}.
refine (
  match x with
  | HdrEth =>
    match y with
    | HdrEth => left eq_refl
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
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h64_eq_dec (x y: header 64) : {x = y} + {x <> y}.
refine (
  match x with
  | HdrIPv4 =>
    match y with
    | HdrIPv4 => left eq_refl
    | HdrIPv6 => right _
    end
  | HdrIPv6 =>
    match y with
    | HdrIPv4 => right _
    | HdrIPv6 => left eq_refl
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
    | HdrTCP => right _
    | HdrUDP => right _
    end
  | HdrVLAN1 =>
    match y with
    | HdrVLAN0 => right _
    | HdrVLAN1 => left eq_refl
    | HdrTCP => right _
    | HdrUDP => right _
    end
  | HdrTCP =>
    match y with
    | HdrVLAN0 => right _
    | HdrVLAN1 => right _
    | HdrTCP => left eq_refl
    | HdrUDP => right _
    end
  | HdrUDP =>
    match y with
    | HdrVLAN0 => right _
    | HdrVLAN1 => right _
    | HdrTCP => right _
    | HdrUDP => left eq_refl
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
      existT _ _ HdrEth
    ; existT _ _ HdrVLAN0
    ; existT _ _ HdrVLAN1
    ; existT _ _ HdrIPv4
    ; existT _ _ HdrIPv6
    ; existT _ _ HdrTCP
    ; existT _ _ HdrUDP
    ; existT _ _ HdrICMP
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
| ParseEth
| ParseVLAN0
| ParseVLAN1
| ParseIPv4
| ParseIPv6
| ParseTCP
| ParseUDP
| ParseICMP.

Scheme Equality for state.
Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
Global Program Instance state_finite: @Finite state _ state_eq_dec :=
  {| enum := [ParseEth; ParseVLAN0; ParseVLAN1; ParseIPv4; ParseIPv6; ParseTCP; ParseUDP; ParseICMP] |}.
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

Program Definition aut: Syntax.t state header :=
  {| t_states := states |}.
Solve Obligations with (destruct s; cbv; Lia.lia).