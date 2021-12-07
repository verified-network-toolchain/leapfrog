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


Module IPOptionsRef10.
  Inductive state :=
  | Parse0
  | Parse1
  | Parse2
  | Parse3
  | Parse4
  | Parse5
  | Parse6
  | Parse7
  | Parse8
  | Parse9

  | Parse01
  | Parse11
  | Parse21
  | Parse31
  | Parse41
  | Parse51
  | Parse61
  | Parse71
  | Parse81
  | Parse91
  
  | Parse02
  | Parse12
  | Parse22
  | Parse32
  | Parse42
  | Parse52
  | Parse62
  | Parse72
  | Parse82
  | Parse92

  | Parse03
  | Parse13
  | Parse23
  | Parse33
  | Parse43
  | Parse53
  | Parse63
  | Parse73
  | Parse83
  | Parse93
  
  | Parse04
  | Parse14
  | Parse24
  | Parse34
  | Parse44
  | Parse54
  | Parse64
  | Parse74
  | Parse84
  | Parse94

  | Parse05
  | Parse15
  | Parse25
  | Parse35
  | Parse45
  | Parse55
  | Parse65
  | Parse75
  | Parse85
  | Parse95

  | Parse06
  | Parse16
  | Parse26
  | Parse36
  | Parse46
  | Parse56
  | Parse66
  | Parse76
  | Parse86
  | Parse96

  | Parse07
  | Parse17
  | Parse27
  | Parse37
  | Parse47
  | Parse57
  | Parse67
  | Parse77
  | Parse87
  | Parse97

  | Parse08
  | Parse18
  | Parse28
  | Parse38
  | Parse48
  | Parse58
  | Parse68
  | Parse78
  | Parse88
  | Parse98.

  Scheme Equality for state.

  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [ Parse0 ; Parse1 ; Parse2 ; Parse3 ; Parse4 ; Parse5 ; Parse6 ; Parse7 ; Parse8 ; Parse9
    ; Parse01 ; Parse11 ; Parse21 ; Parse31 ; Parse41 ; Parse51 ; Parse61 ; Parse71 ; Parse81 ; Parse91
      ; Parse02 ; Parse12 ; Parse22 ; Parse32 ; Parse42 ; Parse52 ; Parse62 ; Parse72 ; Parse82 ; Parse92
    ; Parse03 ; Parse13 ; Parse23 ; Parse33 ; Parse43 ; Parse53 ; Parse63 ; Parse73 ; Parse83 ; Parse93
      ; Parse04 ; Parse14 ; Parse24 ; Parse34 ; Parse44 ; Parse54 ; Parse64 ; Parse74 ; Parse84 ; Parse94
    ; Parse05 ; Parse15 ; Parse25 ; Parse35 ; Parse45 ; Parse55 ; Parse65 ; Parse75 ; Parse85 ; Parse95
    ; Parse06 ; Parse16 ; Parse26 ; Parse36 ; Parse46 ; Parse56 ; Parse66 ; Parse76 ; Parse86 ; Parse96
    ; Parse07 ; Parse17 ; Parse27 ; Parse37 ; Parse47 ; Parse57 ; Parse67 ; Parse77 ; Parse87 ; Parse97
    ; Parse08 ; Parse18 ; Parse28 ; Parse38 ; Parse48 ; Parse58 ; Parse68 ; Parse78 ; Parse88 ; Parse98
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
  | Scratch24 : header 24
  | Scratch32 : header 32
  | Scratch40 : header 40
  | Scratch48 : header 48
  | Scratch56 : header 56
  | T0 : header 8
  | L0 : header 8
  | V0 : header 64
  | T1 : header 8
  | L1 : header 8
  | V1 : header 64
  | T2 : header 8
  | L2 : header 8
  | V2 : header 64
  | T3 : header 8
  | L3 : header 8
  | V3 : header 64
  | T4 : header 8
  | L4 : header 8
  | V4 : header 64
  | T5 : header 8
  | L5 : header 8
  | V5 : header 64
  | T6 : header 8
  | L6 : header 8
  | V6 : header 64
  | T7 : header 8
  | L7 : header 8
  | V7 : header 64
  | T8 : header 8
  | L8 : header 8
  | V8 : header 64
  | T9 : header 8
  | L9 : header 8
  | V9 : header 64.

  Derive Signature for header.

  Definition h8_eq_dec (x y: header 8) : {x = y} + {x <> y}.
    refine (
    match x with 
    | Scratch8 =>
      match y with
      | Scratch8  => left eq_refl
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      | T5 => right _
      | L5 => right _
      | T6 => right _
      | L6 => right _
      | T7 => right _
      | L7 => right _
      | T8 => right _
      | L8 => right _
      | T9 => right _
      | L9 => right _
      end
    | T0 =>
      match y with
      | Scratch8  => right _
      | T0 => left eq_refl
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      | T5 => right _
      | L5 => right _
      | T6 => right _
      | L6 => right _
      | T7 => right _
      | L7 => right _
      | T8 => right _
      | L8 => right _
      | T9 => right _
      | L9 => right _
      end
      
    | L0 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => left eq_refl
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      | T5 => right _
      | L5 => right _
      | T6 => right _
      | L6 => right _
      | T7 => right _
      | L7 => right _
      | T8 => right _
      | L8 => right _
      | T9 => right _
      | L9 => right _
      end
      
    | T1 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => left eq_refl
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      | T5 => right _
      | L5 => right _
      | T6 => right _
      | L6 => right _
      | T7 => right _
      | L7 => right _
      | T8 => right _
      | L8 => right _
      | T9 => right _
      | L9 => right _
      end
      
    | L1 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => left eq_refl
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      | T5 => right _
      | L5 => right _
      | T6 => right _
      | L6 => right _
      | T7 => right _
      | L7 => right _
      | T8 => right _
      | L8 => right _
      | T9 => right _
      | L9 => right _
      end
      
    | T2 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => left eq_refl
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      | T5 => right _
      | L5 => right _
      | T6 => right _
      | L6 => right _
      | T7 => right _
      | L7 => right _
      | T8 => right _
      | L8 => right _
      | T9 => right _
      | L9 => right _
      end
      
    | L2 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => left eq_refl
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      | T5 => right _
      | L5 => right _
      | T6 => right _
      | L6 => right _
      | T7 => right _
      | L7 => right _
      | T8 => right _
      | L8 => right _
      | T9 => right _
      | L9 => right _
      end
      
    | T3 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => left eq_refl
      | L3 => right _
      | T4 => right _
      | L4 => right _
      | T5 => right _
      | L5 => right _
      | T6 => right _
      | L6 => right _
      | T7 => right _
      | L7 => right _
      | T8 => right _
      | L8 => right _
      | T9 => right _
      | L9 => right _
      end
      
    | L3 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => left eq_refl
      | T4 => right _
      | L4 => right _
      | T5 => right _
      | L5 => right _
      | T6 => right _
      | L6 => right _
      | T7 => right _
      | L7 => right _
      | T8 => right _
      | L8 => right _
      | T9 => right _
      | L9 => right _
      end
      
    | T4 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => left eq_refl
      | L4 => right _
      | T5 => right _
      | L5 => right _
      | T6 => right _
      | L6 => right _
      | T7 => right _
      | L7 => right _
      | T8 => right _
      | L8 => right _
      | T9 => right _
      | L9 => right _
      end
      
    | L4 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => left eq_refl
      | T5 => right _
      | L5 => right _
      | T6 => right _
      | L6 => right _
      | T7 => right _
      | L7 => right _
      | T8 => right _
      | L8 => right _
      | T9 => right _
      | L9 => right _
      end
      
    | T5 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      | T5 => left eq_refl
      | L5 => right _
      | T6 => right _
      | L6 => right _
      | T7 => right _
      | L7 => right _
      | T8 => right _
      | L8 => right _
      | T9 => right _
      | L9 => right _
      end
      
    | L5 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      | T5 => right _
      | L5 => left eq_refl
      | T6 => right _
      | L6 => right _
      | T7 => right _
      | L7 => right _
      | T8 => right _
      | L8 => right _
      | T9 => right _
      | L9 => right _
      end
      
    | T6 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      | T5 => right _
      | L5 => right _
      | T6 => left eq_refl
      | L6 => right _
      | T7 => right _
      | L7 => right _
      | T8 => right _
      | L8 => right _
      | T9 => right _
      | L9 => right _
      end
      
    | L6 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      | T5 => right _
      | L5 => right _
      | T6 => right _
      | L6 => left eq_refl
      | T7 => right _
      | L7 => right _
      | T8 => right _
      | L8 => right _
      | T9 => right _
      | L9 => right _
      end
      
    | T7 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      | T5 => right _
      | L5 => right _
      | T6 => right _
      | L6 => right _
      | T7 => left eq_refl
      | L7 => right _
      | T8 => right _
      | L8 => right _
      | T9 => right _
      | L9 => right _
      end
      
    | L7 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      | T5 => right _
      | L5 => right _
      | T6 => right _
      | L6 => right _
      | T7 => right _
      | L7 => left eq_refl
      | T8 => right _
      | L8 => right _
      | T9 => right _
      | L9 => right _
      end
      
    | T8 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      | T5 => right _
      | L5 => right _
      | T6 => right _
      | L6 => right _
      | T7 => right _
      | L7 => right _
      | T8 => left eq_refl
      | L8 => right _
      | T9 => right _
      | L9 => right _
      end
      
    | L8 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      | T5 => right _
      | L5 => right _
      | T6 => right _
      | L6 => right _
      | T7 => right _
      | L7 => right _
      | T8 => right _
      | L8 => left eq_refl
      | T9 => right _
      | L9 => right _
      end
      
    | T9 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      | T5 => right _
      | L5 => right _
      | T6 => right _
      | L6 => right _
      | T7 => right _
      | L7 => right _
      | T8 => right _
      | L8 => right _
      | T9 => left eq_refl
      | L9 => right _
      end
      
    | L9 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      | T5 => right _
      | L5 => right _
      | T6 => right _
      | L6 => right _
      | T7 => right _
      | L7 => right _
      | T8 => right _
      | L8 => right _
      | T9 => right _
      | L9 => left eq_refl
      end
    end
  ); intros H; inversion H.
  Defined.

  Definition h16_eq_dec (x y: header 16) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch16, Scratch16 => left eq_refl
    | _, _ => idProp
    end.
  Definition h24_eq_dec (x y: header 24) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch24, Scratch24 => left eq_refl
    | _, _ => idProp
    end.
  Definition h32_eq_dec (x y: header 32) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch32, Scratch32 => left eq_refl
    | _, _ => idProp
    end.
  Definition h40_eq_dec (x y: header 40) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch40, Scratch40 => left eq_refl
    | _, _ => idProp
    end.
  Definition h48_eq_dec (x y: header 48) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch48, Scratch48 => left eq_refl
    | _, _ => idProp
    end.
  Definition h56_eq_dec (x y: header 56) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch56, Scratch56 => left eq_refl
    | _, _ => idProp
    end.

  Definition h64_eq_dec (x y: header 64) : {x = y} + {x <> y}.
    refine (
    match x with 
    | V0 =>
      match y with
      | V0 => left eq_refl
      | V1 => right _
      | V2 => right _
      | V3 => right _
      | V4 => right _
      | V5 => right _
      | V6 => right _
      | V7 => right _
      | V8 => right _
      | V9 => right _
      end
    | V1 =>
      match y with
      | V0 => right _
      | V1 => left eq_refl
      | V2 => right _
      | V3 => right _
      | V4 => right _
      | V5 => right _
      | V6 => right _
      | V7 => right _
      | V8 => right _
      | V9 => right _
      end
    | V2 =>
      match y with
      | V0 => right _
      | V1 => right _
      | V2 => left eq_refl
      | V3 => right _
      | V4 => right _
      | V5 => right _
      | V6 => right _
      | V7 => right _
      | V8 => right _
      | V9 => right _
      end
    | V3 =>
      match y with
      | V0 => right _
      | V1 => right _
      | V2 => right _
      | V3 => left eq_refl
      | V4 => right _
      | V5 => right _
      | V6 => right _
      | V7 => right _
      | V8 => right _
      | V9 => right _
      end
    | V4 =>
      match y with
      | V0 => right _
      | V1 => right _
      | V2 => right _
      | V3 => right _
      | V4 => left eq_refl
      | V5 => right _
      | V6 => right _
      | V7 => right _
      | V8 => right _
      | V9 => right _
      end
    | V5 =>
      match y with
      | V0 => right _
      | V1 => right _
      | V2 => right _
      | V3 => right _
      | V4 => right _
      | V5 => left eq_refl
      | V6 => right _
      | V7 => right _
      | V8 => right _
      | V9 => right _
      end
    | V6 =>
      match y with
      | V0 => right _
      | V1 => right _
      | V2 => right _
      | V3 => right _
      | V4 => right _
      | V5 => right _
      | V6 => left eq_refl
      | V7 => right _
      | V8 => right _
      | V9 => right _
      end
    | V7 =>
      match y with
      | V0 => right _
      | V1 => right _
      | V2 => right _
      | V3 => right _
      | V4 => right _
      | V5 => right _
      | V6 => right _
      | V7 => left eq_refl
      | V8 => right _
      | V9 => right _
      end
    | V8 =>
      match y with
      | V0 => right _
      | V1 => right _
      | V2 => right _
      | V3 => right _
      | V4 => right _
      | V5 => right _
      | V6 => right _
      | V7 => right _
      | V8 => left eq_refl
      | V9 => right _
      end
    | V9 =>
      match y with
      | V0 => right _
      | V1 => right _
      | V2 => right _
      | V3 => right _
      | V4 => right _
      | V5 => right _
      | V6 => right _
      | V7 => right _
      | V8 => right _
      | V9 => left eq_refl
      end
    end
  ); intros H; inversion H.
  Defined.

  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y 
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h8_eq_dec) :: 
        (existT _ _ h16_eq_dec) :: (existT _ _ h24_eq_dec) :: (existT _ _ h32_eq_dec) :: 
        (existT _ _ h40_eq_dec) :: (existT _ _ h48_eq_dec) :: (existT _ _ h56_eq_dec) ::
        (existT _ _ h64_eq_dec) :: nil).
  Defined. 

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [8; 16; 24; 32; 40; 48; 56; 64].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum :=   [existT _ _ Scratch8 ;
    existT _ _ Scratch16 ;
    existT _ _ Scratch24 ;
    existT _ _ Scratch32 ;
    existT _ _ Scratch40 ;
    existT _ _ Scratch48 ;
    existT _ _ Scratch56 ;
    existT _ _ T0 ;
    existT _ _ L0 ;
    existT _ _ V0 ;
    existT _ _ T1 ;
    existT _ _ L1 ;
    existT _ _ V1 ;
    existT _ _ T2 ;
    existT _ _ L2 ;
    existT _ _ V2 ;
    existT _ _ T3 ;
    existT _ _ L3 ;
    existT _ _ V3 ;
    existT _ _ T4 ;
    existT _ _ L4 ;
    existT _ _ V4 ;
    existT _ _ T5 ;
    existT _ _ L5 ;
    existT _ _ V5 ;
    existT _ _ T6 ;
    existT _ _ L6 ;
    existT _ _ V6 ;
    existT _ _ T7 ;
    existT _ _ L7 ;
    existT _ _ V7 ;
    existT _ _ T8 ;
    existT _ _ L8 ;
    existT _ _ V8 ;
    existT _ _ T9 ;
    existT _ _ L9 ;
    existT _ _ V9 ]; |}.
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
    | Parse0 =>
      {| st_op := 
          extract(T0) ;;
          extract(L0) ;
         st_trans := transition select (| EHdr T0, EHdr L0 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse01 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse02 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse03 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse04 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse05 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse06 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|1 |] ==> inl Parse07 ;;;
           [| *, exact #b|0|0|0|0|1|0|0|0 |] ==> inl Parse08 ;;;
            reject
         }}
      |}
    | Parse01 =>
      {| st_op := 
          extract(Scratch8) ;;
          V0 <- EConcat (m := 56) (EHdr Scratch8) ((EHdr V0)[64--8]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse02 =>
      {| st_op := 
          extract(Scratch16) ;;
          V0 <- EConcat (m := 48) (EHdr Scratch16) ((EHdr V0)[64--16]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse03 =>
      {| st_op := 
          extract(Scratch24) ;;
          V0 <- EConcat (m := 40) (EHdr Scratch24) ((EHdr V0)[64--24]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse04 =>
      {| st_op := 
          extract(Scratch32) ;;
          V0 <- EConcat (m := 32) (EHdr Scratch32) ((EHdr V0)[64--32]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse05 =>
      {| st_op := 
          extract(Scratch40) ;;
          V0 <- EConcat (m := 24) (EHdr Scratch40) ((EHdr V0)[64--40]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse06 =>
      {| st_op := 
          extract(Scratch48) ;;
          V0 <- EConcat (m := 16) (EHdr Scratch48) ((EHdr V0)[64--48]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse07 =>
      {| st_op := 
          extract(Scratch56) ;;
          V0 <- EConcat (m := 8) (EHdr Scratch56) ((EHdr V0)[64--56]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse08 =>
      {| st_op := 
          extract(V0) ;
         st_trans := transition inl Parse1;
      |}

    | Parse1 =>
      {| st_op := 
          extract(T1) ;;
          extract(L1) ;
         st_trans := transition select (| EHdr T1, EHdr L1 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse11 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse12 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse13 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse14 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse15 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse16 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|1 |] ==> inl Parse17 ;;;
           [| *, exact #b|0|0|0|0|1|0|0|0 |] ==> inl Parse18 ;;;
            reject
         }}
      |}
    | Parse11 =>
      {| st_op := 
          extract(Scratch8) ;;
          V1 <- EConcat (m := 56) (EHdr Scratch8) ((EHdr V1)[64--8]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse12 =>
      {| st_op := 
          extract(Scratch16) ;;
          V1 <- EConcat (m := 48) (EHdr Scratch16) ((EHdr V1)[64--16]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse13 =>
      {| st_op := 
          extract(Scratch24) ;;
          V1 <- EConcat (m := 40) (EHdr Scratch24) ((EHdr V1)[64--24]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse14 =>
      {| st_op := 
          extract(Scratch32) ;;
          V1 <- EConcat (m := 32) (EHdr Scratch32) ((EHdr V1)[64--32]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse15 =>
      {| st_op := 
          extract(Scratch40) ;;
          V1 <- EConcat (m := 24) (EHdr Scratch40) ((EHdr V1)[64--40]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse16 =>
      {| st_op := 
          extract(Scratch48) ;;
          V1 <- EConcat (m := 16) (EHdr Scratch48) ((EHdr V1)[64--48]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse17 =>
      {| st_op := 
          extract(Scratch56) ;;
          V1 <- EConcat (m := 8) (EHdr Scratch56) ((EHdr V1)[64--56]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse18 =>
      {| st_op := 
          extract(V1) ;
         st_trans := transition inl Parse2;
      |}

    | Parse2 =>
      {| st_op := 
          extract(T2) ;;
          extract(L2) ;
         st_trans := transition select (| EHdr T2, EHdr L2 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse21 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse22 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse23 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse24 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse25 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse26 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|1 |] ==> inl Parse27 ;;;
           [| *, exact #b|0|0|0|0|1|0|0|0 |] ==> inl Parse28 ;;;
            reject
         }}
      |}
    | Parse21 =>
      {| st_op := 
          extract(Scratch8) ;;
          V1 <- EConcat (m := 56) (EHdr Scratch8) ((EHdr V2)[64--8]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse22 =>
      {| st_op := 
          extract(Scratch16) ;;
          V2 <- EConcat (m := 48) (EHdr Scratch16) ((EHdr V2)[64--16]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse23 =>
      {| st_op := 
          extract(Scratch24) ;;
          V2 <- EConcat (m := 40) (EHdr Scratch24) ((EHdr V2)[64--24]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse24 =>
      {| st_op := 
          extract(Scratch32) ;;
          V2 <- EConcat (m := 32) (EHdr Scratch32) ((EHdr V2)[64--32]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse25 =>
      {| st_op := 
          extract(Scratch40) ;;
          V2 <- EConcat (m := 24) (EHdr Scratch40) ((EHdr V2)[64--40]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse26 =>
      {| st_op := 
          extract(Scratch48) ;;
          V2 <- EConcat (m := 16) (EHdr Scratch48) ((EHdr V2)[64--48]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse27 =>
      {| st_op := 
          extract(Scratch56) ;;
          V2 <- EConcat (m := 8) (EHdr Scratch56) ((EHdr V2)[64--56]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse28 =>
      {| st_op := 
          extract(V2) ;
         st_trans := transition inl Parse3;
      |}

    | Parse3 =>
      {| st_op := 
          extract(T3) ;;
          extract(L3) ;
         st_trans := transition select (| EHdr T3, EHdr L3 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse31 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse32 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse33 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse34 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse35 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse36 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|1 |] ==> inl Parse37 ;;;
           [| *, exact #b|0|0|0|0|1|0|0|0 |] ==> inl Parse38 ;;;
            reject
         }}
      |}
    | Parse31 =>
      {| st_op := 
          extract(Scratch8) ;;
          V3 <- EConcat (m := 56) (EHdr Scratch8) ((EHdr V3)[64--8]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse32 =>
      {| st_op := 
          extract(Scratch16) ;;
          V3 <- EConcat (m := 48) (EHdr Scratch16) ((EHdr V3)[64--16]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse33 =>
      {| st_op := 
          extract(Scratch24) ;;
          V3 <- EConcat (m := 40) (EHdr Scratch24) ((EHdr V3)[64--24]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse34 =>
      {| st_op := 
          extract(Scratch32) ;;
          V3 <- EConcat (m := 32) (EHdr Scratch32) ((EHdr V3)[64--32]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse35 =>
      {| st_op := 
          extract(Scratch40) ;;
          V3 <- EConcat (m := 24) (EHdr Scratch40) ((EHdr V3)[64--40]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse36 =>
      {| st_op := 
          extract(Scratch48) ;;
          V3 <- EConcat (m := 16) (EHdr Scratch48) ((EHdr V3)[64--48]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse37 =>
      {| st_op := 
          extract(Scratch56) ;;
          V3 <- EConcat (m := 8) (EHdr Scratch56) ((EHdr V3)[64--56]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse38 =>
      {| st_op := 
          extract(V3) ;
         st_trans := transition inl Parse4;
      |}
      
    | Parse4 =>
      {| st_op := 
          extract(T4) ;;
          extract(L4) ;
         st_trans := transition select (| EHdr T4, EHdr L4 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse41 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse42 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse43 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse44 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse45 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse46 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|1 |] ==> inl Parse47 ;;;
           [| *, exact #b|0|0|0|0|1|0|0|0 |] ==> inl Parse48 ;;;
            reject
         }}
      |}
    | Parse41 =>
      {| st_op := 
          extract(Scratch8) ;;
          V4 <- EConcat (m := 56) (EHdr Scratch8) ((EHdr V4)[64--8]) ;
         st_trans := transition inl Parse5;
      |}
    | Parse42 =>
      {| st_op := 
          extract(Scratch16) ;;
          V4 <- EConcat (m := 48) (EHdr Scratch16) ((EHdr V4)[64--16]) ;
         st_trans := transition inl Parse5;
      |}
    | Parse43 =>
      {| st_op := 
          extract(Scratch24) ;;
          V4 <- EConcat (m := 40) (EHdr Scratch24) ((EHdr V4)[64--24]) ;
         st_trans := transition inl Parse5;
      |}
    | Parse44 =>
      {| st_op := 
          extract(Scratch32) ;;
          V4 <- EConcat (m := 32) (EHdr Scratch32) ((EHdr V4)[64--32]) ;
         st_trans := transition inl Parse5;
      |}
    | Parse45 =>
      {| st_op := 
          extract(Scratch40) ;;
          V4 <- EConcat (m := 24) (EHdr Scratch40) ((EHdr V4)[64--40]) ;
         st_trans := transition inl Parse5;
      |}
    | Parse46 =>
      {| st_op := 
          extract(Scratch48) ;;
          V4 <- EConcat (m := 16) (EHdr Scratch48) ((EHdr V4)[64--48]) ;
         st_trans := transition inl Parse5;
      |}
    | Parse47 =>
      {| st_op := 
          extract(Scratch56) ;;
          V4 <- EConcat (m := 8) (EHdr Scratch56) ((EHdr V4)[64--56]) ;
         st_trans := transition inl Parse5;
      |}
    | Parse48 =>
      {| st_op := 
          extract(V4) ;
         st_trans := transition inl Parse5;
      |}

    | Parse5 =>
      {| st_op := 
          extract(T5) ;;
          extract(L5) ;
         st_trans := transition select (| EHdr T5, EHdr L5 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse51 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse52 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse53 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse54 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse55 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse56 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|1 |] ==> inl Parse57 ;;;
           [| *, exact #b|0|0|0|0|1|0|0|0 |] ==> inl Parse58 ;;;
            reject
         }}
      |}
    | Parse51 =>
      {| st_op := 
          extract(Scratch8) ;;
          V5 <- EConcat (m := 56) (EHdr Scratch8) ((EHdr V5)[64--8]) ;
         st_trans := transition inl Parse6;
      |}
    | Parse52 =>
      {| st_op := 
          extract(Scratch16) ;;
          V5 <- EConcat (m := 48) (EHdr Scratch16) ((EHdr V5)[64--16]) ;
         st_trans := transition inl Parse6;
      |}
    | Parse53 =>
      {| st_op := 
          extract(Scratch24) ;;
          V5 <- EConcat (m := 40) (EHdr Scratch24) ((EHdr V5)[64--24]) ;
         st_trans := transition inl Parse6;
      |}
    | Parse54 =>
      {| st_op := 
          extract(Scratch32) ;;
          V5 <- EConcat (m := 32) (EHdr Scratch32) ((EHdr V5)[64--32]) ;
         st_trans := transition inl Parse6;
      |}
    | Parse55 =>
      {| st_op := 
          extract(Scratch40) ;;
          V5 <- EConcat (m := 24) (EHdr Scratch40) ((EHdr V5)[64--40]) ;
         st_trans := transition inl Parse6;
      |}
    | Parse56 =>
      {| st_op := 
          extract(Scratch48) ;;
          V5 <- EConcat (m := 16) (EHdr Scratch48) ((EHdr V5)[64--48]) ;
         st_trans := transition inl Parse6;
      |}
    | Parse57 =>
      {| st_op := 
          extract(Scratch56) ;;
          V5 <- EConcat (m := 8) (EHdr Scratch56) ((EHdr V5)[64--56]) ;
         st_trans := transition inl Parse6;
      |}
    | Parse58 =>
      {| st_op := 
          extract(V5) ;
         st_trans := transition inl Parse6;
      |}

    | Parse6 =>
      {| st_op := 
          extract(T6) ;;
          extract(L6) ;
         st_trans := transition select (| EHdr T6, EHdr L6 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse61 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse62 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse63 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse64 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse65 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse66 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|1 |] ==> inl Parse67 ;;;
           [| *, exact #b|0|0|0|0|1|0|0|0 |] ==> inl Parse68 ;;;
            reject
         }}
      |}
    | Parse61 =>
      {| st_op := 
          extract(Scratch8) ;;
          V6 <- EConcat (m := 56) (EHdr Scratch8) ((EHdr V6)[64--8]) ;
         st_trans := transition inl Parse7;
      |}
    | Parse62 =>
      {| st_op := 
          extract(Scratch16) ;;
          V6 <- EConcat (m := 48) (EHdr Scratch16) ((EHdr V6)[64--16]) ;
         st_trans := transition inl Parse7;
      |}
    | Parse63 =>
      {| st_op := 
          extract(Scratch24) ;;
          V6 <- EConcat (m := 40) (EHdr Scratch24) ((EHdr V6)[64--24]) ;
         st_trans := transition inl Parse7;
      |}
    | Parse64 =>
      {| st_op := 
          extract(Scratch32) ;;
          V6 <- EConcat (m := 32) (EHdr Scratch32) ((EHdr V6)[64--32]) ;
         st_trans := transition inl Parse7;
      |}
    | Parse65 =>
      {| st_op := 
          extract(Scratch40) ;;
          V6 <- EConcat (m := 24) (EHdr Scratch40) ((EHdr V6)[64--40]) ;
         st_trans := transition inl Parse7;
      |}
    | Parse66 =>
      {| st_op := 
          extract(Scratch48) ;;
          V6 <- EConcat (m := 16) (EHdr Scratch48) ((EHdr V6)[64--48]) ;
         st_trans := transition inl Parse7;
      |}
    | Parse67 =>
      {| st_op := 
          extract(Scratch56) ;;
          V6 <- EConcat (m := 8) (EHdr Scratch56) ((EHdr V6)[64--56]) ;
         st_trans := transition inl Parse7;
      |}
    | Parse68 =>
      {| st_op := 
          extract(V6) ;
         st_trans := transition inl Parse7;
      |}

    | Parse7 =>
      {| st_op := 
          extract(T7) ;;
          extract(L7) ;
         st_trans := transition select (| EHdr T7, EHdr L7 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse71 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse72 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse73 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse74 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse75 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse76 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|1 |] ==> inl Parse77 ;;;
           [| *, exact #b|0|0|0|0|1|0|0|0 |] ==> inl Parse78 ;;;
            reject
         }}
      |}
    | Parse71 =>
      {| st_op := 
          extract(Scratch8) ;;
          V7 <- EConcat (m := 56) (EHdr Scratch8) ((EHdr V7)[64--8]) ;
         st_trans := transition inl Parse8;
      |}
    | Parse72 =>
      {| st_op := 
          extract(Scratch16) ;;
          V7 <- EConcat (m := 48) (EHdr Scratch16) ((EHdr V7)[64--16]) ;
         st_trans := transition inl Parse8;
      |}
    | Parse73 =>
      {| st_op := 
          extract(Scratch24) ;;
          V7 <- EConcat (m := 40) (EHdr Scratch24) ((EHdr V7)[64--24]) ;
         st_trans := transition inl Parse8;
      |}
    | Parse74 =>
      {| st_op := 
          extract(Scratch32) ;;
          V7 <- EConcat (m := 32) (EHdr Scratch32) ((EHdr V7)[64--32]) ;
         st_trans := transition inl Parse8;
      |}
    | Parse75 =>
      {| st_op := 
          extract(Scratch40) ;;
          V7 <- EConcat (m := 24) (EHdr Scratch40) ((EHdr V7)[64--40]) ;
         st_trans := transition inl Parse8;
      |}
    | Parse76 =>
      {| st_op := 
          extract(Scratch48) ;;
          V7 <- EConcat (m := 16) (EHdr Scratch48) ((EHdr V7)[64--48]) ;
         st_trans := transition inl Parse8;
      |}
    | Parse77 =>
      {| st_op := 
          extract(Scratch56) ;;
          V7 <- EConcat (m := 8) (EHdr Scratch56) ((EHdr V7)[64--56]) ;
         st_trans := transition inl Parse8;
      |}
    | Parse78 =>
      {| st_op := 
          extract(V7) ;
         st_trans := transition inl Parse8;
      |}

    | Parse8 =>
      {| st_op := 
          extract(T8) ;;
          extract(L8) ;
         st_trans := transition select (| EHdr T8, EHdr L8 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse81 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse82 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse83 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse84 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse85 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse86 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|1 |] ==> inl Parse87 ;;;
           [| *, exact #b|0|0|0|0|1|0|0|0 |] ==> inl Parse88 ;;;
            reject
         }}
      |}
    | Parse81 =>
      {| st_op := 
          extract(Scratch8) ;;
          V8 <- EConcat (m := 56) (EHdr Scratch8) ((EHdr V8)[64--8]) ;
         st_trans := transition inl Parse9;
      |}
    | Parse82 =>
      {| st_op := 
          extract(Scratch16) ;;
          V8 <- EConcat (m := 48) (EHdr Scratch16) ((EHdr V8)[64--16]) ;
         st_trans := transition inl Parse9;
      |}
    | Parse83 =>
      {| st_op := 
          extract(Scratch24) ;;
          V8 <- EConcat (m := 40) (EHdr Scratch24) ((EHdr V8)[64--24]) ;
         st_trans := transition inl Parse9;
      |}
    | Parse84 =>
      {| st_op := 
          extract(Scratch32) ;;
          V8 <- EConcat (m := 32) (EHdr Scratch32) ((EHdr V8)[64--32]) ;
         st_trans := transition inl Parse9;
      |}
    | Parse85 =>
      {| st_op := 
          extract(Scratch40) ;;
          V8 <- EConcat (m := 24) (EHdr Scratch40) ((EHdr V8)[64--40]) ;
         st_trans := transition inl Parse9;
      |}
    | Parse86 =>
      {| st_op := 
          extract(Scratch48) ;;
          V8 <- EConcat (m := 16) (EHdr Scratch48) ((EHdr V8)[64--48]) ;
         st_trans := transition inl Parse9;
      |}
    | Parse87 =>
      {| st_op := 
          extract(Scratch56) ;;
          V8 <- EConcat (m := 8) (EHdr Scratch56) ((EHdr V8)[64--56]) ;
         st_trans := transition inl Parse9;
      |}
    | Parse88 =>
      {| st_op := 
          extract(V8) ;
         st_trans := transition inl Parse9;
      |}
    
    | Parse9 =>
      {| st_op := 
          extract(T9) ;;
          extract(L9) ;
         st_trans := transition select (| EHdr T9, EHdr L9 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse91 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse92 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse93 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse94 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse95 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse96 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|1 |] ==> inl Parse97 ;;;
           [| *, exact #b|0|0|0|0|1|0|0|0 |] ==> inl Parse98 ;;;
            reject
         }}
      |}
    | Parse91 =>
      {| st_op := 
          extract(Scratch8) ;;
          V9 <- EConcat (m := 56) (EHdr Scratch8) ((EHdr V9)[64--8]) ;
         st_trans := transition accept;
      |}
    | Parse92 =>
      {| st_op := 
          extract(Scratch16) ;;
          V9 <- EConcat (m := 48) (EHdr Scratch16) ((EHdr V9)[64--16]) ;
         st_trans := transition accept;
      |}
    | Parse93 =>
      {| st_op := 
          extract(Scratch24) ;;
          V9 <- EConcat (m := 40) (EHdr Scratch24) ((EHdr V9)[64--24]) ;
         st_trans := transition accept;
      |}
    | Parse94 =>
      {| st_op := 
          extract(Scratch32) ;;
          V9 <- EConcat (m := 32) (EHdr Scratch32) ((EHdr V9)[64--32]) ;
         st_trans := transition accept;
      |}
    | Parse95 =>
      {| st_op := 
          extract(Scratch40) ;;
          V9 <- EConcat (m := 24) (EHdr Scratch40) ((EHdr V9)[64--40]) ;
         st_trans := transition accept;
      |}
    | Parse96 =>
      {| st_op := 
          extract(Scratch48) ;;
          V9 <- EConcat (m := 16) (EHdr Scratch48) ((EHdr V9)[64--48]) ;
         st_trans := transition accept;
      |}
    | Parse97 =>
      {| st_op := 
          extract(Scratch56) ;;
          V9 <- EConcat (m := 8) (EHdr Scratch56) ((EHdr V9)[64--56]) ;
         st_trans := transition accept;
      |}
    | Parse98 =>
      {| st_op := 
          extract(V9) ;
         st_trans := transition accept;
      |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End IPOptionsRef10.



Module IPOptionsRef5.
  Inductive state :=
  | Parse0
  | Parse1
  | Parse2
  | Parse3
  | Parse4

  | Parse01
  | Parse11
  | Parse21
  | Parse31
  | Parse41
  
  | Parse02
  | Parse12
  | Parse22
  | Parse32
  | Parse42

  | Parse03
  | Parse13
  | Parse23
  | Parse33
  | Parse43

  | Parse04
  | Parse14
  | Parse24
  | Parse34
  | Parse44

  | Parse05
  | Parse15
  | Parse25
  | Parse35
  | Parse45

  | Parse06
  | Parse16
  | Parse26
  | Parse36
  | Parse46

  | Parse07
  | Parse17
  | Parse27
  | Parse37
  | Parse47

  | Parse08
  | Parse18
  | Parse28
  | Parse38
  | Parse48.

  Scheme Equality for state.

  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [ Parse0 ; Parse1 ; Parse2 ; Parse3 ; Parse4
    ; Parse01 ; Parse11 ; Parse21 ; Parse31 ; Parse41
      ; Parse02 ; Parse12 ; Parse22 ; Parse32 ; Parse42
    ; Parse03 ; Parse13 ; Parse23 ; Parse33 ; Parse43
    ; Parse04 ; Parse14 ; Parse24 ; Parse34 ; Parse44
    ; Parse05 ; Parse15 ; Parse25 ; Parse35 ; Parse45
    ; Parse06 ; Parse16 ; Parse26 ; Parse36 ; Parse46
    ; Parse07 ; Parse17 ; Parse27 ; Parse37 ; Parse47
    ; Parse08 ; Parse18 ; Parse28 ; Parse38 ; Parse48 ]; |}.
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
  | Scratch24 : header 24
  | Scratch32 : header 32
  | Scratch40 : header 40
  | Scratch48 : header 48
  | Scratch56 : header 56
  | T0 : header 8
  | L0 : header 8
  | V0 : header 64
  | T1 : header 8
  | L1 : header 8
  | V1 : header 64
  | T2 : header 8
  | L2 : header 8
  | V2 : header 64
  | T3 : header 8
  | L3 : header 8
  | V3 : header 64
  | T4 : header 8
  | L4 : header 8
  | V4 : header 64.

  Derive Signature for header.

  Definition h8_eq_dec (x y: header 8) : {x = y} + {x <> y}.
    refine (
    match x with 
    | Scratch8 =>
      match y with
      | Scratch8  => left eq_refl
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      end
    | T0 =>
      match y with
      | Scratch8  => right _
      | T0 => left eq_refl
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      end
      
    | L0 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => left eq_refl
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      end
      
    | T1 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => left eq_refl
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      end
      
    | L1 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => left eq_refl
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      end
      
    | T2 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => left eq_refl
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      end
      
    | L2 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => left eq_refl
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => right _
      end
      
    | T3 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => left eq_refl
      | L3 => right _
      | T4 => right _
      | L4 => right _
      end
      
    | L3 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => left eq_refl
      | T4 => right _
      | L4 => right _
      end
      
    | T4 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => left eq_refl
      | L4 => right _
      end
      
    | L4 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      | T3 => right _
      | L3 => right _
      | T4 => right _
      | L4 => left eq_refl
      end
    end
  ); intros H; inversion H.
  Defined.

  Definition h16_eq_dec (x y: header 16) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch16, Scratch16 => left eq_refl
    | _, _ => idProp
    end.
  Definition h24_eq_dec (x y: header 24) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch24, Scratch24 => left eq_refl
    | _, _ => idProp
    end.
  Definition h32_eq_dec (x y: header 32) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch32, Scratch32 => left eq_refl
    | _, _ => idProp
    end.
  Definition h40_eq_dec (x y: header 40) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch40, Scratch40 => left eq_refl
    | _, _ => idProp
    end.
  Definition h48_eq_dec (x y: header 48) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch48, Scratch48 => left eq_refl
    | _, _ => idProp
    end.
  Definition h56_eq_dec (x y: header 56) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch56, Scratch56 => left eq_refl
    | _, _ => idProp
    end.

  Definition h64_eq_dec (x y: header 64) : {x = y} + {x <> y}.
    refine (
    match x with 
    | V0 =>
      match y with
      | V0 => left eq_refl
      | V1 => right _
      | V2 => right _
      | V3 => right _
      | V4 => right _
      end
    | V1 =>
      match y with
      | V0 => right _
      | V1 => left eq_refl
      | V2 => right _
      | V3 => right _
      | V4 => right _
      end
    | V2 =>
      match y with
      | V0 => right _
      | V1 => right _
      | V2 => left eq_refl
      | V3 => right _
      | V4 => right _
      end
    | V3 =>
      match y with
      | V0 => right _
      | V1 => right _
      | V2 => right _
      | V3 => left eq_refl
      | V4 => right _
      end
    | V4 =>
      match y with
      | V0 => right _
      | V1 => right _
      | V2 => right _
      | V3 => right _
      | V4 => left eq_refl
      end
    end
  ); intros H; inversion H.
  Defined.

  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y 
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h8_eq_dec) :: 
        (existT _ _ h16_eq_dec) :: (existT _ _ h24_eq_dec) :: (existT _ _ h32_eq_dec) :: 
        (existT _ _ h40_eq_dec) :: (existT _ _ h48_eq_dec) :: (existT _ _ h56_eq_dec) ::
        (existT _ _ h64_eq_dec) :: nil).
  Defined. 

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [8; 16; 24; 32; 40; 48; 56; 64].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum :=   [existT _ _ Scratch8 ;
    existT _ _ Scratch16 ;
    existT _ _ Scratch24 ;
    existT _ _ Scratch32 ;
    existT _ _ Scratch40 ;
    existT _ _ Scratch48 ;
    existT _ _ Scratch56 ;
    existT _ _ T0 ;
    existT _ _ L0 ;
    existT _ _ V0 ;
    existT _ _ T1 ;
    existT _ _ L1 ;
    existT _ _ V1 ;
    existT _ _ T2 ;
    existT _ _ L2 ;
    existT _ _ V2 ;
    existT _ _ T3 ;
    existT _ _ L3 ;
    existT _ _ V3 ;
    existT _ _ T4 ;
    existT _ _ L4 ;
    existT _ _ V4 
    ]; |}.
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
    | Parse0 =>
      {| st_op := 
          extract(T0) ;;
          extract(L0) ;
         st_trans := transition select (| EHdr T0, EHdr L0 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse01 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse02 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse03 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse04 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse05 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse06 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|1 |] ==> inl Parse07 ;;;
           [| *, exact #b|0|0|0|0|1|0|0|0 |] ==> inl Parse08 ;;;
            reject
         }}
      |}
    | Parse01 =>
      {| st_op := 
          extract(Scratch8) ;;
          V0 <- EConcat (m := 56) (EHdr Scratch8) ((EHdr V0)[64--8]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse02 =>
      {| st_op := 
          extract(Scratch16) ;;
          V0 <- EConcat (m := 48) (EHdr Scratch16) ((EHdr V0)[64--16]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse03 =>
      {| st_op := 
          extract(Scratch24) ;;
          V0 <- EConcat (m := 40) (EHdr Scratch24) ((EHdr V0)[64--24]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse04 =>
      {| st_op := 
          extract(Scratch32) ;;
          V0 <- EConcat (m := 32) (EHdr Scratch32) ((EHdr V0)[64--32]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse05 =>
      {| st_op := 
          extract(Scratch40) ;;
          V0 <- EConcat (m := 24) (EHdr Scratch40) ((EHdr V0)[64--40]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse06 =>
      {| st_op := 
          extract(Scratch48) ;;
          V0 <- EConcat (m := 16) (EHdr Scratch48) ((EHdr V0)[64--48]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse07 =>
      {| st_op := 
          extract(Scratch56) ;;
          V0 <- EConcat (m := 8) (EHdr Scratch56) ((EHdr V0)[64--56]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse08 =>
      {| st_op := 
          extract(V0) ;
         st_trans := transition inl Parse1;
      |}

    | Parse1 =>
      {| st_op := 
          extract(T1) ;;
          extract(L1) ;
         st_trans := transition select (| EHdr T1, EHdr L1 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse11 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse12 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse13 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse14 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse15 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse16 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|1 |] ==> inl Parse17 ;;;
           [| *, exact #b|0|0|0|0|1|0|0|0 |] ==> inl Parse18 ;;;
            reject
         }}
      |}
    | Parse11 =>
      {| st_op := 
          extract(Scratch8) ;;
          V1 <- EConcat (m := 56) (EHdr Scratch8) ((EHdr V1)[64--8]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse12 =>
      {| st_op := 
          extract(Scratch16) ;;
          V1 <- EConcat (m := 48) (EHdr Scratch16) ((EHdr V1)[64--16]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse13 =>
      {| st_op := 
          extract(Scratch24) ;;
          V1 <- EConcat (m := 40) (EHdr Scratch24) ((EHdr V1)[64--24]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse14 =>
      {| st_op := 
          extract(Scratch32) ;;
          V1 <- EConcat (m := 32) (EHdr Scratch32) ((EHdr V1)[64--32]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse15 =>
      {| st_op := 
          extract(Scratch40) ;;
          V1 <- EConcat (m := 24) (EHdr Scratch40) ((EHdr V1)[64--40]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse16 =>
      {| st_op := 
          extract(Scratch48) ;;
          V1 <- EConcat (m := 16) (EHdr Scratch48) ((EHdr V1)[64--48]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse17 =>
      {| st_op := 
          extract(Scratch56) ;;
          V1 <- EConcat (m := 8) (EHdr Scratch56) ((EHdr V1)[64--56]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse18 =>
      {| st_op := 
          extract(V1) ;
         st_trans := transition inl Parse2;
      |}

    | Parse2 =>
      {| st_op := 
          extract(T2) ;;
          extract(L2) ;
         st_trans := transition select (| EHdr T2, EHdr L2 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse21 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse22 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse23 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse24 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse25 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse26 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|1 |] ==> inl Parse27 ;;;
           [| *, exact #b|0|0|0|0|1|0|0|0 |] ==> inl Parse28 ;;;
            reject
         }}
      |}
    | Parse21 =>
      {| st_op := 
          extract(Scratch8) ;;
          V1 <- EConcat (m := 56) (EHdr Scratch8) ((EHdr V2)[64--8]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse22 =>
      {| st_op := 
          extract(Scratch16) ;;
          V2 <- EConcat (m := 48) (EHdr Scratch16) ((EHdr V2)[64--16]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse23 =>
      {| st_op := 
          extract(Scratch24) ;;
          V2 <- EConcat (m := 40) (EHdr Scratch24) ((EHdr V2)[64--24]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse24 =>
      {| st_op := 
          extract(Scratch32) ;;
          V2 <- EConcat (m := 32) (EHdr Scratch32) ((EHdr V2)[64--32]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse25 =>
      {| st_op := 
          extract(Scratch40) ;;
          V2 <- EConcat (m := 24) (EHdr Scratch40) ((EHdr V2)[64--40]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse26 =>
      {| st_op := 
          extract(Scratch48) ;;
          V2 <- EConcat (m := 16) (EHdr Scratch48) ((EHdr V2)[64--48]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse27 =>
      {| st_op := 
          extract(Scratch56) ;;
          V2 <- EConcat (m := 8) (EHdr Scratch56) ((EHdr V2)[64--56]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse28 =>
      {| st_op := 
          extract(V2) ;
         st_trans := transition inl Parse3;
      |}

    | Parse3 =>
      {| st_op := 
          extract(T3) ;;
          extract(L3) ;
         st_trans := transition select (| EHdr T3, EHdr L3 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse31 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse32 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse33 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse34 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse35 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse36 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|1 |] ==> inl Parse37 ;;;
           [| *, exact #b|0|0|0|0|1|0|0|0 |] ==> inl Parse38 ;;;
            reject
         }}
      |}
    | Parse31 =>
      {| st_op := 
          extract(Scratch8) ;;
          V3 <- EConcat (m := 56) (EHdr Scratch8) ((EHdr V3)[64--8]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse32 =>
      {| st_op := 
          extract(Scratch16) ;;
          V3 <- EConcat (m := 48) (EHdr Scratch16) ((EHdr V3)[64--16]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse33 =>
      {| st_op := 
          extract(Scratch24) ;;
          V3 <- EConcat (m := 40) (EHdr Scratch24) ((EHdr V3)[64--24]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse34 =>
      {| st_op := 
          extract(Scratch32) ;;
          V3 <- EConcat (m := 32) (EHdr Scratch32) ((EHdr V3)[64--32]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse35 =>
      {| st_op := 
          extract(Scratch40) ;;
          V3 <- EConcat (m := 24) (EHdr Scratch40) ((EHdr V3)[64--40]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse36 =>
      {| st_op := 
          extract(Scratch48) ;;
          V3 <- EConcat (m := 16) (EHdr Scratch48) ((EHdr V3)[64--48]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse37 =>
      {| st_op := 
          extract(Scratch56) ;;
          V3 <- EConcat (m := 8) (EHdr Scratch56) ((EHdr V3)[64--56]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse38 =>
      {| st_op := 
          extract(V3) ;
         st_trans := transition inl Parse4;
      |}
      
    | Parse4 =>
      {| st_op := 
          extract(T4) ;;
          extract(L4) ;
         st_trans := transition select (| EHdr T4, EHdr L4 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse41 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse42 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse43 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse44 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse45 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse46 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|1 |] ==> inl Parse47 ;;;
           [| *, exact #b|0|0|0|0|1|0|0|0 |] ==> inl Parse48 ;;;
            reject
         }}
      |}
    | Parse41 =>
      {| st_op := 
          extract(Scratch8) ;;
          V4 <- EConcat (m := 56) (EHdr Scratch8) ((EHdr V4)[64--8]) ;
         st_trans := transition accept;
      |}
    | Parse42 =>
      {| st_op := 
          extract(Scratch16) ;;
          V4 <- EConcat (m := 48) (EHdr Scratch16) ((EHdr V4)[64--16]) ;
         st_trans := transition accept;
      |}
    | Parse43 =>
      {| st_op := 
          extract(Scratch24) ;;
          V4 <- EConcat (m := 40) (EHdr Scratch24) ((EHdr V4)[64--24]) ;
         st_trans := transition accept;
      |}
    | Parse44 =>
      {| st_op := 
          extract(Scratch32) ;;
          V4 <- EConcat (m := 32) (EHdr Scratch32) ((EHdr V4)[64--32]) ;
         st_trans := transition accept;
      |}
    | Parse45 =>
      {| st_op := 
          extract(Scratch40) ;;
          V4 <- EConcat (m := 24) (EHdr Scratch40) ((EHdr V4)[64--40]) ;
         st_trans := transition accept;
      |}
    | Parse46 =>
      {| st_op := 
          extract(Scratch48) ;;
          V4 <- EConcat (m := 16) (EHdr Scratch48) ((EHdr V4)[64--48]) ;
         st_trans := transition accept;
      |}
    | Parse47 =>
      {| st_op := 
          extract(Scratch56) ;;
          V4 <- EConcat (m := 8) (EHdr Scratch56) ((EHdr V4)[64--56]) ;
         st_trans := transition accept;
      |}
    | Parse48 =>
      {| st_op := 
          extract(V4) ;
         st_trans := transition accept;
      |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End IPOptionsRef5.



Module IPOptionsRef2.
  Inductive state :=
  | Parse0
  | Parse1

  | Parse01
  | Parse11
  
  | Parse02
  | Parse12

  | Parse03
  | Parse13

  | Parse04
  | Parse14

  | Parse05
  | Parse15

  | Parse06
  | Parse16

  | Parse07
  | Parse17

  | Parse08
  | Parse18.

  Scheme Equality for state.

  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [  Parse0 ; Parse1
    ; Parse01 ; Parse11
      ; Parse02 ; Parse12
    ; Parse03 ; Parse13
    ; Parse04 ; Parse14
    ; Parse05 ; Parse15
    ; Parse06 ; Parse16
    ; Parse07 ; Parse17
    ; Parse08 ; Parse18 ]; |}.
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
  | Scratch24 : header 24
  | Scratch32 : header 32
  | Scratch40 : header 40
  | Scratch48 : header 48
  | Scratch56 : header 56
  | T0 : header 8
  | L0 : header 8
  | V0 : header 64
  | T1 : header 8
  | L1 : header 8
  | V1 : header 64.

  Derive Signature for header.

  Definition h8_eq_dec (x y: header 8) : {x = y} + {x <> y}.
    refine (
    match x with 
    | Scratch8 =>
      match y with
      | Scratch8  => left eq_refl
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      end
    | T0 =>
      match y with
      | Scratch8  => right _
      | T0 => left eq_refl
      | L0 => right _
      | T1 => right _
      | L1 => right _
      end
      
    | L0 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => left eq_refl
      | T1 => right _
      | L1 => right _
      end
      
    | T1 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => left eq_refl
      | L1 => right _
      end
      
    | L1 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => left eq_refl
      end
    end
  ); intros H; inversion H.
  Defined.

  Definition h16_eq_dec (x y: header 16) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch16, Scratch16 => left eq_refl
    | _, _ => idProp
    end.
  Definition h24_eq_dec (x y: header 24) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch24, Scratch24 => left eq_refl
    | _, _ => idProp
    end.
  Definition h32_eq_dec (x y: header 32) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch32, Scratch32 => left eq_refl
    | _, _ => idProp
    end.
  Definition h40_eq_dec (x y: header 40) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch40, Scratch40 => left eq_refl
    | _, _ => idProp
    end.
  Definition h48_eq_dec (x y: header 48) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch48, Scratch48 => left eq_refl
    | _, _ => idProp
    end.
  Definition h56_eq_dec (x y: header 56) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch56, Scratch56 => left eq_refl
    | _, _ => idProp
    end.

  Definition h64_eq_dec (x y: header 64) : {x = y} + {x <> y}.
    refine (
    match x with 
    | V0 =>
      match y with
      | V0 => left eq_refl
      | V1 => right _
      end
    | V1 =>
      match y with
      | V0 => right _
      | V1 => left eq_refl
      end
    end
  ); intros H; inversion H.
  Defined.

  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y 
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h8_eq_dec) :: 
        (existT _ _ h16_eq_dec) :: (existT _ _ h24_eq_dec) :: (existT _ _ h32_eq_dec) :: 
        (existT _ _ h40_eq_dec) :: (existT _ _ h48_eq_dec) :: (existT _ _ h56_eq_dec) ::
        (existT _ _ h64_eq_dec) :: nil).
  Defined. 

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [8; 16; 24; 32; 40; 48; 56; 64].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum :=   [existT _ _ Scratch8 ;
    existT _ _ Scratch16 ;
    existT _ _ Scratch24 ;
    existT _ _ Scratch32 ;
    existT _ _ Scratch40 ;
    existT _ _ Scratch48 ;
    existT _ _ Scratch56 ;
    existT _ _ T0 ;
    existT _ _ L0 ;
    existT _ _ V0 ;
    existT _ _ T1 ;
    existT _ _ L1 ;
    existT _ _ V1 
    ]; |}.
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
    | Parse0 =>
      {| st_op := 
          extract(T0) ;;
          extract(L0) ;
         st_trans := transition select (| EHdr T0, EHdr L0 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse01 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse02 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse03 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse04 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse05 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse06 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|1 |] ==> inl Parse07 ;;;
           [| *, exact #b|0|0|0|0|1|0|0|0 |] ==> inl Parse08 ;;;
            reject
         }}
      |}
    | Parse01 =>
      {| st_op := 
          extract(Scratch8) ;;
          V0 <- EConcat (m := 56) (EHdr Scratch8) ((EHdr V0)[64--8]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse02 =>
      {| st_op := 
          extract(Scratch16) ;;
          V0 <- EConcat (m := 48) (EHdr Scratch16) ((EHdr V0)[64--16]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse03 =>
      {| st_op := 
          extract(Scratch24) ;;
          V0 <- EConcat (m := 40) (EHdr Scratch24) ((EHdr V0)[64--24]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse04 =>
      {| st_op := 
          extract(Scratch32) ;;
          V0 <- EConcat (m := 32) (EHdr Scratch32) ((EHdr V0)[64--32]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse05 =>
      {| st_op := 
          extract(Scratch40) ;;
          V0 <- EConcat (m := 24) (EHdr Scratch40) ((EHdr V0)[64--40]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse06 =>
      {| st_op := 
          extract(Scratch48) ;;
          V0 <- EConcat (m := 16) (EHdr Scratch48) ((EHdr V0)[64--48]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse07 =>
      {| st_op := 
          extract(Scratch56) ;;
          V0 <- EConcat (m := 8) (EHdr Scratch56) ((EHdr V0)[64--56]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse08 =>
      {| st_op := 
          extract(V0) ;
         st_trans := transition inl Parse1;
      |}

    | Parse1 =>
      {| st_op := 
          extract(T1) ;;
          extract(L1) ;
         st_trans := transition select (| EHdr T1, EHdr L1 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse11 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse12 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse13 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse14 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse15 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse16 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|1 |] ==> inl Parse17 ;;;
           [| *, exact #b|0|0|0|0|1|0|0|0 |] ==> inl Parse18 ;;;
            reject
         }}
      |}
    | Parse11 =>
      {| st_op := 
          extract(Scratch8) ;;
          V1 <- EConcat (m := 56) (EHdr Scratch8) ((EHdr V1)[64--8]) ;
         st_trans := transition accept;
      |}
    | Parse12 =>
      {| st_op := 
          extract(Scratch16) ;;
          V1 <- EConcat (m := 48) (EHdr Scratch16) ((EHdr V1)[64--16]) ;
         st_trans := transition accept;
      |}
    | Parse13 =>
      {| st_op := 
          extract(Scratch24) ;;
          V1 <- EConcat (m := 40) (EHdr Scratch24) ((EHdr V1)[64--24]) ;
         st_trans := transition accept;
      |}
    | Parse14 =>
      {| st_op := 
          extract(Scratch32) ;;
          V1 <- EConcat (m := 32) (EHdr Scratch32) ((EHdr V1)[64--32]) ;
         st_trans := transition accept;
      |}
    | Parse15 =>
      {| st_op := 
          extract(Scratch40) ;;
          V1 <- EConcat (m := 24) (EHdr Scratch40) ((EHdr V1)[64--40]) ;
         st_trans := transition accept;
      |}
    | Parse16 =>
      {| st_op := 
          extract(Scratch48) ;;
          V1 <- EConcat (m := 16) (EHdr Scratch48) ((EHdr V1)[64--48]) ;
         st_trans := transition accept;
      |}
    | Parse17 =>
      {| st_op := 
          extract(Scratch56) ;;
          V1 <- EConcat (m := 8) (EHdr Scratch56) ((EHdr V1)[64--56]) ;
         st_trans := transition accept;
      |}
    | Parse18 =>
      {| st_op := 
          extract(V1) ;
         st_trans := transition accept;
      |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End IPOptionsRef2.


Module IPOptions32.
  Inductive state :=
  | Parse0
  | Parse1

  | Parse01
  | Parse11
  
  | Parse02
  | Parse12

  | Parse03
  | Parse13.

  Scheme Equality for state.

  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [  Parse0 ; Parse1
    ; Parse01 ; Parse11
      ; Parse02 ; Parse12
    ; Parse03 ; Parse13 ]; |}.
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
  | T0 : header 8
  | L0 : header 8
  | V0 : header 24
  | T1 : header 8
  | L1 : header 8
  | V1 : header 24.

  Derive Signature for header.

  Definition h8_eq_dec (x y: header 8) : {x = y} + {x <> y}.
    refine (
    match x with 
    | Scratch8 =>
      match y with
      | Scratch8  => left eq_refl
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      end
    | T0 =>
      match y with
      | Scratch8  => right _
      | T0 => left eq_refl
      | L0 => right _
      | T1 => right _
      | L1 => right _
      end
      
    | L0 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => left eq_refl
      | T1 => right _
      | L1 => right _
      end
      
    | T1 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => left eq_refl
      | L1 => right _
      end
      
    | L1 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => left eq_refl
      end
    end
  ); intros H; inversion H.
  Defined.

  Definition h16_eq_dec (x y: header 16) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch16, Scratch16 => left eq_refl
    | _, _ => idProp
    end.

  Definition h24_eq_dec (x y: header 24) : {x = y} + {x <> y}.
  refine (
    match x with 
    | V0 =>
      match y with
      | V0  => left eq_refl
      | V1 => right _
      end
    | V1 =>
      match y with
      | V0  => right _
      | V1 => left eq_refl
      end
    end
  ); intros H; inversion H.
  Defined.

  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y 
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h8_eq_dec) :: 
        (existT _ _ h16_eq_dec) :: (existT _ _ h24_eq_dec) :: nil).
  Defined. 

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [8; 16; 24].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum :=   [existT _ _ Scratch8 ;
    existT _ _ Scratch16 ;
    existT _ _ T0 ;
    existT _ _ L0 ;
    existT _ _ V0 ;
    existT _ _ T1 ;
    existT _ _ L1 ;
    existT _ _ V1 
    ]; |}.
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
    | Parse0 =>
      {| st_op := 
          extract(T0) ;;
          extract(L0) ;
         st_trans := transition select (| EHdr T0, EHdr L0 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse01 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse02 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse03 ;;;
            reject
         }}
      |}
    | Parse01 =>
      {| st_op := 
          extract(Scratch8) ;;
          V0 <- EConcat (m := 16) (EHdr Scratch8) ((EHdr V0)[24--8]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse02 =>
      {| st_op := 
          extract(Scratch16) ;;
          V0 <- EConcat (m := 8) (EHdr Scratch16) ((EHdr V0)[24--16]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse03 =>
      {| st_op := 
          extract(V0) ;
         st_trans := transition inl Parse1;
      |}
    | Parse1 =>
      {| st_op := 
          extract(T1) ;;
          extract(L1) ;
         st_trans := transition select (| EHdr T1, EHdr L1 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse11 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse12 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse13 ;;;
            reject
         }}
      |}
    | Parse11 =>
      {| st_op := 
          extract(Scratch8) ;;
          V1 <- EConcat (m := 16) (EHdr Scratch8) ((EHdr V1)[24--8]) ;
         st_trans := transition accept;
      |}
    | Parse12 =>
      {| st_op := 
          extract(Scratch16) ;;
          V1 <- EConcat (m := 8) (EHdr Scratch16) ((EHdr V1)[24--16]) ;
         st_trans := transition accept;
      |}
    | Parse13 =>
      {| st_op := 
          extract(V1) ;
         st_trans := transition accept;
      |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End IPOptions32.

Module IPOptionsSpec32.
  Inductive state :=
  | Parse0
  | Parse1

  | Parse01
  | Parse11
  
  | Parse02
  | Parse12

  | Parse03
  | Parse13

  | Parse0S
  | Parse1S.

  Scheme Equality for state.

  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [  Parse0 ; Parse1
    ; Parse01 ; Parse11
      ; Parse02 ; Parse12
    ; Parse03 ; Parse13;
    Parse0S; Parse1S ]; |}.
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
  | Scratch24 : header 24
  | T0 : header 8
  | L0 : header 8
  | T1 : header 8
  | L1 : header 8
  | V: header 16.

  Derive Signature for header.

  Definition h8_eq_dec (x y: header 8) : {x = y} + {x <> y}.
    refine (
    match x with 
    | Scratch8 =>
      match y with
      | Scratch8  => left eq_refl
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      end
    | T0 =>
      match y with
      | Scratch8  => right _
      | T0 => left eq_refl
      | L0 => right _
      | T1 => right _
      | L1 => right _
      end
      
    | L0 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => left eq_refl
      | T1 => right _
      | L1 => right _
      end
      
    | T1 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => left eq_refl
      | L1 => right _
      end
      
    | L1 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => left eq_refl
      end
    end
  ); intros H; inversion H.
  Defined.

  Definition h16_eq_dec (x y: header 16) : {x = y} + {x <> y}.
  refine (
    match x with 
    | V =>
      match y with
      | V  => left eq_refl
      | Scratch16 => right _
      end
    | Scratch16 =>
      match y with
      | V  => right _
      | Scratch16 => left eq_refl
      end
    end
  ); intros H; inversion H.
  Defined.

  Definition h24_eq_dec (x y: header 24) : {x = y} + {x <> y} := 
    match x, y with 
    | Scratch24, Scratch24 => left eq_refl
    | _, _ => idProp
    end.

  

  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y 
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h8_eq_dec) :: 
        (existT _ _ h16_eq_dec) :: (existT _ _ h24_eq_dec) :: nil).
  Defined. 

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [8; 16; 24].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum :=   [existT _ _ Scratch8 ;
    existT _ _ Scratch16 ;
    existT _ _ Scratch24 ;
    existT _ _ T0 ;
    existT _ _ L0 ;
    existT _ _ T1 ;
    existT _ _ L1 ;
    existT _ _ V
    ]; |}.
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
    | Parse0 =>
      {| st_op := 
          extract(T0) ;;
          extract(L0) ;
         st_trans := transition select (| EHdr T0, EHdr L0 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|1|0|0, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse0S ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse01 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse02 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse03 ;;;
            reject
         }}
      |}
    | Parse01 =>
      {| st_op := 
          extract(Scratch8) ;
         st_trans := transition inl Parse1;
      |}
    | Parse02 =>
      {| st_op := 
          extract(Scratch16) ;
         st_trans := transition inl Parse1;
      |}
    | Parse03 =>
      {| st_op := 
          extract(Scratch24) ;
         st_trans := transition inl Parse1;
      |}
    | Parse0S =>
      {| st_op := 
          extract(V) ;
         st_trans := transition inl Parse1;
      |}
    | Parse1 =>
      {| st_op := 
          extract(T1) ;;
          extract(L1) ;
         st_trans := transition select (| EHdr T1, EHdr L1 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|1|0|0, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse1S ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse11 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse12 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse13 ;;;
            reject
         }}
      |}
    | Parse11 =>
      {| st_op := 
          extract(Scratch8) ;
         st_trans := transition accept;
      |}
    | Parse12 =>
      {| st_op := 
          extract(Scratch16) ;
         st_trans := transition accept;
      |}
    | Parse1S =>
      {| st_op := 
          extract(V) ;
         st_trans := transition accept;
      |}
    | Parse13 =>
      {| st_op := 
          extract(Scratch24) ;
         st_trans := transition accept;
      |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End IPOptionsSpec32.


(* parse 2 options of between 0-6 bytes *)
Module IPOptionsRef62.
  Inductive state :=
  | Parse0
  | Parse1

  | Parse01
  | Parse11
  
  | Parse02
  | Parse12

  | Parse03
  | Parse13

  | Parse04
  | Parse14

  | Parse05
  | Parse15

  | Parse06
  | Parse16.

  Scheme Equality for state.

  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [  Parse0 ; Parse1
    ; Parse01 ; Parse11
      ; Parse02 ; Parse12
    ; Parse03 ; Parse13
    ; Parse04 ; Parse14
    ; Parse05 ; Parse15
    ; Parse06 ; Parse16 ]; |}.
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
  | Scratch24 : header 24
  | Scratch32 : header 32
  | Scratch40 : header 40
  | T0 : header 8
  | L0 : header 8
  | V0 : header 48
  | T1 : header 8
  | L1 : header 8
  | V1 : header 48.

  Derive Signature for header.

  Definition h8_eq_dec (x y: header 8) : {x = y} + {x <> y}.
    refine (
    match x with 
    | Scratch8 =>
      match y with
      | Scratch8  => left eq_refl
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      end
    | T0 =>
      match y with
      | Scratch8  => right _
      | T0 => left eq_refl
      | L0 => right _
      | T1 => right _
      | L1 => right _
      end
      
    | L0 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => left eq_refl
      | T1 => right _
      | L1 => right _
      end
      
    | T1 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => left eq_refl
      | L1 => right _
      end
    | L1 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => left eq_refl
      end
    end
  ); intros H; inversion H.
  Defined.

  Definition h16_eq_dec (x y: header 16) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch16, Scratch16 => left eq_refl
    end.
  Definition h24_eq_dec (x y: header 24) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch24, Scratch24 => left eq_refl
    end.
  Definition h32_eq_dec (x y: header 32) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch32, Scratch32 => left eq_refl
    end.
  Definition h40_eq_dec (x y: header 40) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch40, Scratch40 => left eq_refl
    end.

  Definition h48_eq_dec (x y: header 48) : {x = y} + {x <> y}.
    refine (
    match x with 
    | V0 =>
      match y with
      | V0 => left eq_refl
      | V1 => right _
      end
    | V1 =>
      match y with
      | V0 => right _
      | V1 => left eq_refl
      end
    end
  ); intros H; inversion H.
  Defined.

  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y 
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h8_eq_dec) :: 
        (existT _ _ h16_eq_dec) :: (existT _ _ h24_eq_dec) :: (existT _ _ h32_eq_dec) :: 
        (existT _ _ h40_eq_dec) :: (existT _ _ h48_eq_dec) :: nil).
  Defined. 

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [8; 16; 24; 32; 40; 48].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum :=   [existT _ _ Scratch8 ;
    existT _ _ Scratch16 ;
    existT _ _ Scratch24 ;
    existT _ _ Scratch32 ;
    existT _ _ Scratch40 ;
    existT _ _ T0 ;
    existT _ _ L0 ;
    existT _ _ V0 ;
    existT _ _ T1 ;
    existT _ _ L1 ;
    existT _ _ V1 
    ]; |}.
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
    | Parse0 =>
      {| st_op := 
          extract(T0) ;;
          extract(L0) ;
         st_trans := transition select (| EHdr T0, EHdr L0 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse01 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse02 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse03 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse04 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse05 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse06 ;;;
            reject
         }}
      |}
    | Parse01 =>
      {| st_op := 
          extract(Scratch8) ;;
          V0 <- EConcat (m := 40) (EHdr Scratch8) ((EHdr V0)[48--8]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse02 =>
      {| st_op := 
          extract(Scratch16) ;;
          V0 <- EConcat (m := 32) (EHdr Scratch16) ((EHdr V0)[48--16]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse03 =>
      {| st_op := 
          extract(Scratch24) ;;
          V0 <- EConcat (m := 24) (EHdr Scratch24) ((EHdr V0)[48--24]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse04 =>
      {| st_op := 
          extract(Scratch32) ;;
          V0 <- EConcat (m := 16) (EHdr Scratch32) ((EHdr V0)[48--32]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse05 =>
      {| st_op := 
          extract(Scratch40) ;;
          V0 <- EConcat (m := 8) (EHdr Scratch40) ((EHdr V0)[48--40]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse06 =>
      {| st_op := 
          extract(V0) ;
         st_trans := transition inl Parse1;
      |}

    | Parse1 =>
      {| st_op := 
          extract(T1) ;;
          extract(L1) ;
         st_trans := transition select (| EHdr T1, EHdr L1 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse11 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse12 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse13 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse14 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse15 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse16 ;;;
            reject
         }}
      |}
    | Parse11 =>
      {| st_op := 
          extract(Scratch8) ;;
          V1 <- EConcat (m := 40) (EHdr Scratch8) ((EHdr V1)[48--8]) ;
         st_trans := transition accept;
      |}
    | Parse12 =>
      {| st_op := 
          extract(Scratch16) ;;
          V1 <- EConcat (m := 32) (EHdr Scratch16) ((EHdr V1)[48--16]) ;
         st_trans := transition accept;
      |}
    | Parse13 =>
      {| st_op := 
          extract(Scratch24) ;;
          V1 <- EConcat (m := 24) (EHdr Scratch24) ((EHdr V1)[48--24]) ;
         st_trans := transition accept;
      |}
    | Parse14 =>
      {| st_op := 
          extract(Scratch32) ;;
          V1 <- EConcat (m := 16) (EHdr Scratch32) ((EHdr V1)[48--32]) ;
         st_trans := transition accept;
      |}
    | Parse15 =>
      {| st_op := 
          extract(Scratch40) ;;
          V1 <- EConcat (m := 8) (EHdr Scratch40) ((EHdr V1)[48--40]) ;
         st_trans := transition accept;
      |}
    | Parse16 =>
      {| st_op := 
          extract(V1) ;
         st_trans := transition accept;
      |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End IPOptionsRef62.

(* parse 3 options of between 0-6 bytes *)
Module IPOptionsRef63.
  Inductive state :=
  | Parse0
  | Parse1
  | Parse2

  | Parse01
  | Parse11
  | Parse21
  
  | Parse02
  | Parse12
  | Parse22

  | Parse03
  | Parse13
  | Parse23

  | Parse04
  | Parse14
  | Parse24

  | Parse05
  | Parse15
  | Parse25

  | Parse06
  | Parse16
  | Parse26.

  Scheme Equality for state.

  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [  Parse0 ; Parse1; Parse2
    ; Parse01 ; Parse11; Parse21
      ; Parse02 ; Parse12; Parse22
    ; Parse03 ; Parse13; Parse23
    ; Parse04 ; Parse14; Parse24
    ; Parse05 ; Parse15; Parse25
    ; Parse06 ; Parse16; Parse26 ]; |}.
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
  | Scratch24 : header 24
  | Scratch32 : header 32
  | Scratch40 : header 40
  | T0 : header 8
  | L0 : header 8
  | V0 : header 48
  | T1 : header 8
  | L1 : header 8
  | V1 : header 48
  | T2 : header 8
  | L2 : header 8
  | V2 : header 48.

  Derive Signature for header.

  Definition h8_eq_dec (x y: header 8) : {x = y} + {x <> y}.
    refine (
    match x with 
    | Scratch8 =>
      match y with
      | Scratch8  => left eq_refl
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      end
    | T0 =>
      match y with
      | Scratch8  => right _
      | T0 => left eq_refl
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      end
      
    | L0 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => left eq_refl
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => right _
      end
      
    | T1 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => left eq_refl
      | L1 => right _
      | T2 => right _
      | L2 => right _
      end
      
    | L1 =>
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => left eq_refl
      | T2 => right _
      | L2 => right _
      end
    | T2 => 
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => left eq_refl
      | L2 => right _
      end
    | L2 => 
      match y with
      | Scratch8  => right _
      | T0 => right _
      | L0 => right _
      | T1 => right _
      | L1 => right _
      | T2 => right _
      | L2 => left eq_refl
      end
    end
  ); intros H; inversion H.
  Defined.

  Definition h16_eq_dec (x y: header 16) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch16, Scratch16 => left eq_refl
    | _, _ => idProp
    end.
  Definition h24_eq_dec (x y: header 24) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch24, Scratch24 => left eq_refl
    | _, _ => idProp
    end.
  Definition h32_eq_dec (x y: header 32) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch32, Scratch32 => left eq_refl
    | _, _ => idProp
    end.
  Definition h40_eq_dec (x y: header 40) : {x = y} + {x <> y} :=
    match x, y with 
    | Scratch40, Scratch40 => left eq_refl
    | _, _ => idProp
    end.

  Definition h48_eq_dec (x y: header 48) : {x = y} + {x <> y}.
    refine (
    match x with 
    | V0 =>
      match y with
      | V0 => left eq_refl
      | V1 => right _
      | V2 => right _
      end
    | V1 =>
      match y with
      | V0 => right _
      | V1 => left eq_refl
      | V2 => right _
      end
    | V2 => 
      match y with
      | V0 => right _
      | V1 => right _
      | V2 => left eq_refl
      end
    end
  ); intros H; inversion H.
  Defined.

  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y 
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h8_eq_dec) :: 
        (existT _ _ h16_eq_dec) :: (existT _ _ h24_eq_dec) :: (existT _ _ h32_eq_dec) :: 
        (existT _ _ h40_eq_dec) :: (existT _ _ h48_eq_dec) :: nil).
  Defined. 

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [8; 16; 24; 32; 40; 48].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum :=   [existT _ _ Scratch8 ;
    existT _ _ Scratch16 ;
    existT _ _ Scratch24 ;
    existT _ _ Scratch32 ;
    existT _ _ Scratch40 ;
    existT _ _ T0 ;
    existT _ _ L0 ;
    existT _ _ V0 ;
    existT _ _ T1 ;
    existT _ _ L1 ;
    existT _ _ V1 ;
    existT _ _ T2 ;
    existT _ _ L2 ;
    existT _ _ V2 
    ]; |}.
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
    | Parse0 =>
      {| st_op := 
          extract(T0) ;;
          extract(L0) ;
         st_trans := transition select (| EHdr T0, EHdr L0 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse01 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse02 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse03 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse04 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse05 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse06 ;;;
            reject
         }}
      |}
    | Parse01 =>
      {| st_op := 
          extract(Scratch8) ;;
          V0 <- EConcat (m := 40) (EHdr Scratch8) ((EHdr V0)[48--8]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse02 =>
      {| st_op := 
          extract(Scratch16) ;;
          V0 <- EConcat (m := 32) (EHdr Scratch16) ((EHdr V0)[48--16]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse03 =>
      {| st_op := 
          extract(Scratch24) ;;
          V0 <- EConcat (m := 24) (EHdr Scratch24) ((EHdr V0)[48--24]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse04 =>
      {| st_op := 
          extract(Scratch32) ;;
          V0 <- EConcat (m := 16) (EHdr Scratch32) ((EHdr V0)[48--32]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse05 =>
      {| st_op := 
          extract(Scratch40) ;;
          V0 <- EConcat (m := 8) (EHdr Scratch40) ((EHdr V0)[48--40]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse06 =>
      {| st_op := 
          extract(V0) ;
         st_trans := transition inl Parse1;
      |}

    | Parse1 =>
      {| st_op := 
          extract(T1) ;;
          extract(L1) ;
         st_trans := transition select (| EHdr T1, EHdr L1 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse11 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse12 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse13 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse14 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse15 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse16 ;;;
            reject
         }}
      |}
    | Parse11 =>
      {| st_op := 
          extract(Scratch8) ;;
          V1 <- EConcat (m := 40) (EHdr Scratch8) ((EHdr V1)[48--8]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse12 =>
      {| st_op := 
          extract(Scratch16) ;;
          V1 <- EConcat (m := 32) (EHdr Scratch16) ((EHdr V1)[48--16]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse13 =>
      {| st_op := 
          extract(Scratch24) ;;
          V1 <- EConcat (m := 24) (EHdr Scratch24) ((EHdr V1)[48--24]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse14 =>
      {| st_op := 
          extract(Scratch32) ;;
          V1 <- EConcat (m := 16) (EHdr Scratch32) ((EHdr V1)[48--32]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse15 =>
      {| st_op := 
          extract(Scratch40) ;;
          V1 <- EConcat (m := 8) (EHdr Scratch40) ((EHdr V1)[48--40]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse16 =>
      {| st_op := 
          extract(V1) ;
         st_trans := transition inl Parse2;
      |}

    | Parse2 =>
      {| st_op := 
          extract(T2) ;;
          extract(L2) ;
         st_trans := transition select (| EHdr T2, EHdr L2 |) {{
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse21 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse22 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse23 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse24 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse25 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse26 ;;;
            reject
         }}
      |}
    | Parse21 =>
      {| st_op := 
          extract(Scratch8) ;;
          V1 <- EConcat (m := 40) (EHdr Scratch8) ((EHdr V2)[48--8]) ;
         st_trans := transition accept;
      |}
    | Parse22 =>
      {| st_op := 
          extract(Scratch16) ;;
          V2 <- EConcat (m := 32) (EHdr Scratch16) ((EHdr V2)[48--16]) ;
         st_trans := transition accept;
      |}
    | Parse23 =>
      {| st_op := 
          extract(Scratch24) ;;
          V2 <- EConcat (m := 24) (EHdr Scratch24) ((EHdr V2)[48--24]) ;
         st_trans := transition accept;
      |}
    | Parse24 =>
      {| st_op := 
          extract(Scratch32) ;;
          V2 <- EConcat (m := 16) (EHdr Scratch32) ((EHdr V2)[48--32]) ;
         st_trans := transition accept;
      |}
    | Parse25 =>
      {| st_op := 
          extract(Scratch40) ;;
          V2 <- EConcat (m := 8) (EHdr Scratch40) ((EHdr V2)[48--40]) ;
         st_trans := transition accept;
      |}
    | Parse26 =>
      {| st_op := 
          extract(V2) ;
         st_trans := transition accept;
      |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End IPOptionsRef63.