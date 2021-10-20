Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.Syntax.

Require Import Poulet4.P4automata.Notations.
Require Import Poulet4.P4automata.BisimChecker.

Require Import Coq.Arith.PeanoNat.

Open Scope p4a.

Ltac prep_equiv :=
  unfold Equivalence.equiv, RelationClasses.complement in *;
  program_simpl; try congruence.

Obligation Tactic := prep_equiv.

Module Reference.
  Inductive state: Set :=
  | SPref
  | SDest
  | SSrc
  | SProto.

  Scheme Equality for state.

  Global Program Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.

  Global Program Instance state_finite: @Finite state _ state_eqdec :=
    {| enum := [SPref; SDest; SSrc; SProto] |}.
  Next Obligation.
    repeat constructor; eauto with datatypes;
    cbn;
    intuition congruence.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Inductive header: nat ->  Type :=
  | HPref : header 64
  | HDest : header 48
  | HSrc : header 48
  | HProto : header 16.


  Derive Signature for header.

  Definition h64_eq_dec (x y: header 64) : {x = y} + {x <> y} := 
    match x, y with 
    | HPref, HPref => left eq_refl
    | _, _ => idProp
    end.
  Definition h48_eq_dec (x y: header 48) : {x = y} + {x <> y}. 
    refine (match x, y with 
    | HDest, HDest => left eq_refl
    | HSrc, HSrc => left eq_refl
    | HSrc, HDest => right _
    | HDest, HSrc => right _
    | _, _ => idProp
    end);
    intros H; inversion H.
    Defined.

  Definition h16_eq_dec (x y: header 16) : {x = y} + {x <> y} := 
    match x, y with 
    | HProto, HProto => left eq_refl
    | _, _ => idProp
    end.


  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y 
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) 64 h64_eq_dec) :: (existT _ 48 h48_eq_dec) :: ( existT _ 16 h16_eq_dec) :: nil).
  Defined. 

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [64; 48; 16].
  Qed.


  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ HPref ; existT _ _ HDest ; existT _ _ HSrc; existT _ _ HProto ] |}.
  Next Obligation.
    solve_header_finite.
  Qed.
  Next Obligation.
  unfold List.In.
  repeat match goal with 
  | X: {_ & _} |- _ => destruct X
  | X: header _ |- _ =>
    dependent destruction X; subst;
    repeat match goal with
    | |- _ \/ _ => (now left; trivial) || right
    end
  end.
  Qed.




  Definition states (s: state) := 
    match s with 
    | SPref => {| st_op := extract(HPref);
                  st_trans := transition (inl SDest) |}
    | SDest => {| st_op := extract(HDest);
                  st_trans := transition (inl SSrc) |}
    | SSrc => {| st_op := extract(HSrc);
                  st_trans := transition (inl SProto) |}
    | SProto => {| st_op := extract(HProto);
                  st_trans := transition select (| EHdr HProto |) {{
                    [| exact #b|1|0|0|0|0|0|0|0|0|0|0|0|0|0|0|0 |] ==> accept ;;;
                      reject
                  }}
                |}
    end.
  

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).
  
End Reference. 

Module Combined.
  Inductive state :=
  | Parse.
  
  Global Instance state_eqdec: EquivDec.EqDec state eq.
    vm_compute.
    intros.
    left.
    destruct x; destruct x0; trivial.
  Defined.

  Global Program Instance state_finite: @Finite state _ state_eqdec :=
    {| enum := [Parse] |}.
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
  | HdrVar : header 176.

  Derive Signature for header.

  Definition h176_eq_dec (x y: header 176) : {x = y} + {x <> y} := 
    match x, y with 
    | HdrVar, HdrVar => left eq_refl
    end.

  Local Obligation Tactic := intros.
  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y 
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) 176 h176_eq_dec) :: nil).
  Defined. 
  
  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [176].
  Qed.


  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ HdrVar ] |}.
  Next Obligation.
    solve_header_finite.
  Qed.
  Next Obligation.
  unfold List.In.
  repeat match goal with 
  | X: {_ & _} |- _ => destruct X
  | X: header _ |- _ =>
    dependent destruction X; subst;
    repeat match goal with
    | |- _ \/ _ => (now left; trivial) || right
    end
  end.
  Qed.

  Definition states (s: state) :=
    match s with
    | Parse =>
      {| st_op := extract(HdrVar);
        st_trans := transition select (| (EHdr HdrVar)[176 -- 160] |) {{
          [| exact #b|1|0|0|0|0|0|0|0|0|0|0|0|0|0|0|0 |] ==> accept ;;;
            @reject state
        }}
      |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).
  
End Combined.

Module RefComb.
  Definition aut := sum Reference.aut Combined.aut.
End RefComb.
