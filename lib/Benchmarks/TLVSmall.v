Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Leapfrog.Syntax.
Require Import Leapfrog.FinType.
Require Import Leapfrog.Sum.
Require Import Leapfrog.Notations.

Require Import Leapfrog.BisimChecker.

Open Scope p4a.

Ltac prep_equiv :=
  unfold Equivalence.equiv, RelationClasses.complement in *;
  program_simpl; try congruence.

Obligation Tactic := prep_equiv.


Module TLVRefSmall.
  Inductive state :=
  | Parse1
  | Parse2
  | Parse3
  | Parse11
  | Parse21
  | Parse31
  | Parse12
  | Parse22
  | Parse32
  | Parse13
  | Parse23
  | Parse33.

  Scheme Equality for state.

  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [Parse1; Parse2; Parse3;
        Parse11; Parse21; Parse31; 
        Parse12; Parse22; Parse32; 
        Parse13; Parse23; Parse33
        ]; |}.
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
  | Scratch8 : header 8
  | Scratch16 : header 16
  | T1 : header 6
  | L1 : header 2
  | V1 : header 24
  | T2 : header 6
  | L2 : header 2
  | V2 : header 24
  | T3 : header 6
  | L3 : header 2
  | V3 : header 24.

  Derive Signature for header.

  Definition h2_eq_dec (x y: header 2) : {x = y} + {x <> y}.
    refine (
    match x with 
    | L1 => 
      match y with 
      | L1 => left eq_refl
      | L2 => right _
      | L3 => right _
      end
    | L2 => 
      match y with 
      | L1 => right _
      | L2 => left eq_refl
      | L3 => right _
      end
    | L3 => 
      match y with 
      | L1 => right _
      | L2 => right _
      | L3 => left eq_refl
      end
    end
  ); intros H; inversion H.
  Defined.

  Definition h6_eq_dec (x y: header 6) : {x = y} + {x <> y}.
    refine (
    match x with 
    | T1 => 
      match y with 
      | T1 => left eq_refl
      | T2 => right _
      | T3 => right _
      end
    | T2 => 
      match y with 
      | T1 => right _
      | T2 => left eq_refl
      | T3 => right _
      end
    | T3 => 
      match y with 
      | T1 => right _
      | T2 => right _
      | T3 => left eq_refl
      end
    end
  ); intros H; inversion H.
  Defined.

  Definition h8_eq_dec (x y: header 8) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch8, Scratch8 => left eq_refl
    | _, _ => idProp
    end.

  Definition h16_eq_dec (x y: header 16) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch16, Scratch16 => left eq_refl
    | _, _ => idProp
    end.

  Definition h24_eq_dec (x y: header 24) : {x = y} + {x <> y}.
    refine (
    match x with 
    | V1 => 
      match y with 
      | V1 => left eq_refl
      | V2 => right _
      | V3 => right _
      end
    | V2 => 
      match y with 
      | V1 => right _
      | V2 => left eq_refl
      | V3 => right _
      end
    | V3 => 
      match y with 
      | V1 => right _
      | V2 => right _
      | V3 => left eq_refl
      end
    end
  ); intros H; inversion H.
  Defined.

  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y 
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h2_eq_dec) :: 
        (existT _ _ h6_eq_dec) :: (existT _ _ h8_eq_dec) :: (existT _ _ h16_eq_dec) :: (existT _ _ h24_eq_dec) :: nil).
  Defined. 

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [24; 16; 8; 6; 2].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ 
        existT _ _ Scratch8; existT _ _ Scratch16; 
        existT _ _ T1; existT _ _ L1;  existT _ _ V1;
        existT _ _ T2; existT _ _ L2;  existT _ _ V2;
        existT _ _ T3; existT _ _ L3;  existT _ _ V3]; |}.
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

  Definition states (s: state) :=
    match s with
    | Parse1 =>
      {| st_op := 
          extract(T1) ;;
          extract(L1) ;
         st_trans := transition select (| EHdr T1, EHdr L1 |) {{
           [| exact #b|0|0|0|0|0|0, exact #b|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|1, exact #b|0|0 |] ==> accept ;;;
           [| *, exact #b|0|1 |] ==> inl Parse11 ;;;
           [| *, exact #b|1|0 |] ==> inl Parse12 ;;;
           [| *, exact #b|1|1 |] ==> inl Parse13 ;;;
            reject
         }}
      |}
    | Parse11 =>
      {| st_op := 
          extract(Scratch8) ;;
          V1 <- EConcat (m := 16) (EHdr Scratch8) ((EHdr V1)[24--8]); 
         st_trans := transition (inl Parse2)
      |}
    | Parse12 =>
      {| st_op := 
          extract(Scratch16) ;;
          V1 <- EConcat (m := 8) (EHdr Scratch16) ((EHdr V1)[24--16]); 
         st_trans := transition (inl Parse2)
      |}
    | Parse13 =>
      {| st_op := extract(V1) ;
         st_trans := transition (inl Parse2)
      |}

    | Parse2 =>
      {| st_op := 
          extract(T2) ;;
          extract(L2) ;
         st_trans := transition select (| EHdr T2, EHdr L2 |) {{
           [| exact #b|0|0|0|0|0|0, exact #b|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|1, exact #b|0|0 |] ==> accept ;;;
           [| *, exact #b|0|1 |] ==> inl Parse21 ;;;
           [| *, exact #b|1|0 |] ==> inl Parse22 ;;;
           [| *, exact #b|1|1 |] ==> inl Parse23 ;;;
            reject
         }}
      |}
    | Parse21 =>
      {| st_op := 
          extract(Scratch8) ;;
          V1 <- EConcat (m := 16) (EHdr Scratch8) ((EHdr V2)[24--8]); 
         st_trans := transition (inl Parse3)
      |}
    | Parse22 =>
      {| st_op := 
          extract(Scratch16) ;;
          V1 <- EConcat (m := 8) (EHdr Scratch16) ((EHdr V2)[24--16]); 
         st_trans := transition (inl Parse3)
      |}
    | Parse23 =>
      {| st_op := extract(V2) ;
         st_trans := transition (inl Parse3)
      |}

    | Parse3 =>
      {| st_op := 
          extract(T3) ;;
          extract(L3) ;
         st_trans := transition select (| EHdr T3, EHdr L3 |) {{
           [| exact #b|0|0|0|0|0|0, exact #b|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|1, exact #b|0|0 |] ==> accept ;;;
           [| *, exact #b|0|1 |] ==> inl Parse31 ;;;
           [| *, exact #b|1|0 |] ==> inl Parse32 ;;;
           [| *, exact #b|1|1 |] ==> inl Parse33 ;;;
            reject
         }}
      |}
    | Parse31 =>
      {| st_op := 
          extract(Scratch8) ;;
          V1 <- EConcat (m := 16) (EHdr Scratch8) ((EHdr V3)[24--8]); 
         st_trans := transition accept
      |}
    | Parse32 =>
      {| st_op := 
          extract(Scratch16) ;;
          V1 <- EConcat (m := 8) (EHdr Scratch16) ((EHdr V3)[24--16]); 
         st_trans := transition accept
      |}
    | Parse33 =>
      {| st_op := extract(V2) ;
         st_trans := transition accept
      |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End TLVRefSmall.

