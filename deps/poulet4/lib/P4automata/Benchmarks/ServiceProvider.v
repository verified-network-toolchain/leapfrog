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
Notation mpls_size := 32.
Notation ipv4_size := 156.
Notation ipv6_size := 316.

Inductive header: nat -> Type :=
| HdrEth: header eth_size
| HdrMPLS0: header mpls_size
| HdrMPLS1: header mpls_size
| HdrMPLS2: header mpls_size
| HdrMPLS3: header mpls_size
| HdrMPLS4: header mpls_size
| HdrMPLS5: header mpls_size
| HdrIPVer: header 4
| HdrIPv4: header ipv4_size
| HdrIPv6: header ipv6_size.
Derive Signature for header.
Definition h32_eq_dec (x y: header 32) : {x = y} + {x <> y}.
refine (
  match x with
  | HdrMPLS0 =>
    match y with
    | HdrMPLS0 => left eq_refl
    | HdrMPLS1 => right _
    | HdrMPLS2 => right _
    | HdrMPLS3 => right _
    | HdrMPLS4 => right _
    | HdrMPLS5 => right _
    end
  | HdrMPLS1 =>
    match y with
    | HdrMPLS0 => right _
    | HdrMPLS1 => left eq_refl
    | HdrMPLS2 => right _
    | HdrMPLS3 => right _
    | HdrMPLS4 => right _
    | HdrMPLS5 => right _
    end
  | HdrMPLS2 =>
    match y with
    | HdrMPLS0 => right _
    | HdrMPLS1 => right _
    | HdrMPLS2 => left eq_refl
    | HdrMPLS3 => right _
    | HdrMPLS4 => right _
    | HdrMPLS5 => right _
    end
  | HdrMPLS3 =>
    match y with
    | HdrMPLS0 => right _
    | HdrMPLS1 => right _
    | HdrMPLS2 => right _
    | HdrMPLS3 => left eq_refl
    | HdrMPLS4 => right _
    | HdrMPLS5 => right _
    end
  | HdrMPLS4 =>
    match y with
    | HdrMPLS0 => right _
    | HdrMPLS1 => right _
    | HdrMPLS2 => right _
    | HdrMPLS3 => right _
    | HdrMPLS4 => left eq_refl
    | HdrMPLS5 => right _
    end
  | HdrMPLS5 =>
    match y with
    | HdrMPLS0 => right _
    | HdrMPLS1 => right _
    | HdrMPLS2 => right _
    | HdrMPLS3 => right _
    | HdrMPLS4 => right _
    | HdrMPLS5 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h4_eq_dec (x y: header 4) : {x = y} + {x <> y}.
refine (
  match x with
  | HdrIPVer =>
    match y with
    | HdrIPVer => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
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
Definition h316_eq_dec (x y: header 316) : {x = y} + {x <> y}.
refine (
  match x with
  | HdrIPv6 =>
    match y with
    | HdrIPv6 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h156_eq_dec (x y: header 156) : {x = y} + {x <> y}.
refine (
  match x with
  | HdrIPv4 =>
    match y with
    | HdrIPv4 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
  solve_header_eqdec_ n x y
    ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h32_eq_dec) ::
     (existT _ _ h4_eq_dec) ::
     (existT _ _ h112_eq_dec) ::
     (existT _ _ h316_eq_dec) ::
     (existT _ _ h156_eq_dec) ::
      nil).
Defined.

Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.
Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  solve_eqdec'.
Defined.
Global Instance header_finite: forall n, @Finite (header n) _ _.
  intros n; solve_indexed_finiteness n [32; 4 ; 112 ; 316 ; 156 ].
Qed.

Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
  {| enum := [
      existT _ _ HdrEth
    ; existT _ _ HdrMPLS0
    ; existT _ _ HdrMPLS1
    ; existT _ _ HdrMPLS2
    ; existT _ _ HdrMPLS3
    ; existT _ _ HdrMPLS4
    ; existT _ _ HdrMPLS5
    ; existT _ _ HdrIPVer
    ; existT _ _ HdrIPv4
    ; existT _ _ HdrIPv6
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
| ParseMPLS0
| ParseMPLS1
| ParseMPLS2
| ParseMPLS3
| ParseMPLS4
| ParseMPLS5
| ParseIPVer
| ParseIPv4
| ParseIPv6.

Definition states (s: state) : P4A.state state header :=
  match s with
  | ParseEth =>
    {| st_op := extract(HdrEth);
       st_trans := transition select (| (EHdr HdrEth)[111--96] |)
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
       st_trans := transition select (| (EHdr HdrMPLS1)[24--24] |)
                              {{ [| hexact 0 |] ==> inl ParseMPLS2 ;;;
                                 [| hexact 1 |] ==> inl ParseIPVer ;;;
                                 reject
                              }}
    |}
  | ParseMPLS2 => 
    {| st_op := extract(HdrMPLS2);
       st_trans := transition select (| (EHdr HdrMPLS2)[24--24] |)
                              {{ [| hexact 0 |] ==> inl ParseMPLS3 ;;;
                                 [| hexact 1 |] ==> inl ParseIPVer ;;;
                                 reject
                              }}
    |}
  | ParseMPLS3 => 
    {| st_op := extract(HdrMPLS3);
       st_trans := transition select (| (EHdr HdrMPLS3)[24--24] |)
                              {{ [| hexact 0 |] ==> inl ParseMPLS4 ;;;
                                 [| hexact 1 |] ==> inl ParseIPVer ;;;
                                 reject
                              }}
    |}
  | ParseMPLS4 => 
    {| st_op := extract(HdrMPLS4);
       st_trans := transition select (| (EHdr HdrMPLS4)[24--24] |)
                              {{ [| hexact 0 |] ==> inl ParseMPLS5 ;;;
                                 [| hexact 1 |] ==> inl ParseIPVer ;;;
                                 reject
                              }}
    |}
  | ParseMPLS5 => 
    {| st_op := extract(HdrMPLS5);
       st_trans := transition select (| (EHdr HdrMPLS5)[24--24] |)
                              {{ [| hexact 1 |] ==> inl ParseIPVer ;;;
                                 reject
                              }}
    |}
  | ParseIPVer =>
    {| st_op := extract(HdrIPVer);
       st_trans := transition select (| EHdr HdrIPVer |)
                              {{ [| exact #b|0|1|0|0 |] ==> inl ParseIPv4;;;
                                 [| exact #b|0|1|1|0 |] ==> inl ParseIPv6;;;
                                 reject
                              }}
    |}
  | ParseIPv4 =>
    {| st_op := extract(HdrIPv4);
       st_trans := transition accept |}
  | ParseIPv6 =>
    {| st_op := extract(HdrIPv6);
       st_trans := transition accept |}
  end.

Scheme Equality for state.
Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
Global Program Instance state_finite: @Finite state _ state_eq_dec :=
  {| enum := [ParseEth; ParseMPLS0; ParseMPLS1; ParseMPLS2; ParseMPLS3; ParseMPLS4; ParseMPLS5; ParseIPVer; ParseIPv4; ParseIPv6] |}.
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
Solve Obligations with (destruct s; cbv; Lia.lia).