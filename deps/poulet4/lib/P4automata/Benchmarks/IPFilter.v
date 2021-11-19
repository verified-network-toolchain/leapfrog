Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.Syntax.

Require Import Poulet4.P4automata.BisimChecker.

Require Import Poulet4.P4automata.Notations.

Open Scope p4a.

Ltac prep_equiv :=
  unfold Equivalence.equiv, RelationClasses.complement in *;
  program_simpl; try congruence.

Obligation Tactic := prep_equiv.

Module UDPInterleaved.
  Inductive state :=
  | ParseIP
  | ParseUDP
  | ParseTCP.
  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [ParseIP; ParseUDP; ParseTCP] |}.
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

  Inductive header : nat -> Type :=
  | HdrIP : header 64
  | HdrUDP : header 32
  | HdrTCP : header 64.

  Derive Signature for header.

  Definition h64_eq_dec (x y: header 64) : {x = y} + {x <> y}.
  refine (
    match x with
    | HdrIP =>
      match y with
      | HdrIP => left eq_refl
      | HdrTCP => right _
      end
    | HdrTCP => 
      match y with
      | HdrIP => right _
      | HdrTCP => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Definition h32_eq_dec (x y: header 32) : {x = y} + {x <> y}.
  refine (
    match x with
    | HdrUDP =>
      match y with
      | HdrUDP => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  

  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h64_eq_dec) ::
      (existT _ _ h32_eq_dec) ::
        nil).
  Defined.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [32; 64].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ HdrIP ; existT _ _ HdrUDP; existT _ _ HdrTCP ] |}.
  Next Obligation.
    repeat constructor;
    unfold "~";
    intros;
    destruct H;
    now inversion H || now inversion H0.
  Qed.
  Next Obligation.
  dependent destruction X; subst;
  repeat (
    match goal with
    | |- ?L \/ ?R => (now left; trivial) || right
    end
  ).
  Qed.


  Definition states (s: state) :=
    match s with
    | ParseIP =>
      {| st_op := extract(HdrIP);
         st_trans := transition select (| (EHdr HdrIP)[43 -- 40] |) {{
           [| exact #b|0|0|0|1 |] ==> inl ParseUDP ;;;
           [| exact #b|0|0|0|0 |] ==> inl ParseTCP ;;;
            reject
         }};
      |}
    | ParseUDP =>
      {| st_op := extract(HdrUDP);
         st_trans := transition accept |}
    | ParseTCP =>
      {| st_op := extract(HdrTCP);
        st_trans := transition accept |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End UDPInterleaved.

Module UDPCombined.
  Inductive state :=
  | ParsePref
  | ParseSuf.
  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eqdec :=
    {| enum := [ParsePref; ParseSuf] |}.
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

  
  Inductive header : nat -> Type :=
  | HdrIP : header 64
  | HdrPref : header 32.

  Derive Signature for header.

  Definition h64_eq_dec (x y: header 64) : {x = y} + {x <> y}.
  refine (
    match x with
    | HdrIP =>
      match y with
      | HdrIP => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Definition h32_eq_dec (x y: header 32) : {x = y} + {x <> y}.
  refine (
    match x with
    | HdrPref =>
      match y with
      | HdrPref => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.

  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h64_eq_dec) ::
      (existT _ _ h32_eq_dec) ::
        nil).
  Defined.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [32; 64].
  Qed.

  Definition states (s: state) :=
    match s with
    | ParsePref =>
      {| st_op := 
          extract(HdrIP) ;;
          extract(HdrPref) ;
          st_trans := transition select (| (EHdr HdrIP)[43 -- 40] |) {{
            [| exact #b|0|0|0|1 |] ==> accept ;;;
            [| exact #b|0|0|0|0 |] ==> inl ParseSuf ;;;
             reject
          }};
      |}
    | ParseSuf => {| 
      st_op := extract(HdrPref);
      st_trans := transition accept;
    |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End UDPCombined.

Module IPFilter.
  Definition aut := Sum.sum UDPCombined.aut UDPInterleaved.aut.
End IPFilter.