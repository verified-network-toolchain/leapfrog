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
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Scratch8
  | Scratch16
  | Scratch24
  | Scratch32
  | Scratch40
  | Scratch48
  | Scratch56
  | T0
  | L0
  | V0
  | T1
  | L1
  | V1
  | T2
  | L2
  | V2
  | T3
  | L3
  | V3
  | T4
  | L4
  | V4
  | T5
  | L5
  | V5
  | T6
  | L6
  | V6
  | T7
  | L7
  | V7
  | T8
  | L8
  | V8
  | T9
  | L9
  | V9.

  Definition sz (h: header) : nat :=
    match h with
    | Scratch8 => 8
    | Scratch16 => 16
    | Scratch24 => 24
    | Scratch32 => 32
    | Scratch40 => 40
    | Scratch48 => 48
    | Scratch56 => 56
    | T0 | L0
    | T1 | L1
    | T2 | L2
    | T3 | L3
    | T4 | L4
    | T5 | L5
    | T6 | L6
    | T7 | L7
    | T8 | L8
    | T9 | L9 => 8
    | V0
    | V1
    | V2
    | V3
    | V4
    | V5
    | V6
    | V7
    | V8
    | V9 => 64
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) :=
    match s with
    | Parse0 =>
      {| st_op :=
          extract(T0) ;;
          extract(L0) ;
         st_trans := transition select (| EHdr (sz := sz)T0, EHdr (sz := sz)L0 |) {{
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
          V0 <- EConcat (m := 56) (EHdr (sz := sz)Scratch8) ((EHdr (sz := sz)V0)[64--8]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse02 =>
      {| st_op :=
          extract(Scratch16) ;;
          V0 <- EConcat (m := 48) (EHdr (sz := sz)Scratch16) ((EHdr (sz := sz)V0)[64--16]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse03 =>
      {| st_op :=
          extract(Scratch24) ;;
          V0 <- EConcat (m := 40) (EHdr (sz := sz)Scratch24) ((EHdr (sz := sz)V0)[64--24]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse04 =>
      {| st_op :=
          extract(Scratch32) ;;
          V0 <- EConcat (m := 32) (EHdr (sz := sz)Scratch32) ((EHdr (sz := sz)V0)[64--32]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse05 =>
      {| st_op :=
          extract(Scratch40) ;;
          V0 <- EConcat (m := 24) (EHdr (sz := sz)Scratch40) ((EHdr (sz := sz)V0)[64--40]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse06 =>
      {| st_op :=
          extract(Scratch48) ;;
          V0 <- EConcat (m := 16) (EHdr (sz := sz)Scratch48) ((EHdr (sz := sz)V0)[64--48]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse07 =>
      {| st_op :=
          extract(Scratch56) ;;
          V0 <- EConcat (m := 8) (EHdr (sz := sz)Scratch56) ((EHdr (sz := sz)V0)[64--56]) ;
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
         st_trans := transition select (| EHdr (sz := sz)T1, EHdr (sz := sz)L1 |) {{
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
          V1 <- EConcat (m := 56) (EHdr (sz := sz)Scratch8) ((EHdr (sz := sz)V1)[64--8]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse12 =>
      {| st_op :=
          extract(Scratch16) ;;
          V1 <- EConcat (m := 48) (EHdr (sz := sz)Scratch16) ((EHdr (sz := sz)V1)[64--16]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse13 =>
      {| st_op :=
          extract(Scratch24) ;;
          V1 <- EConcat (m := 40) (EHdr (sz := sz)Scratch24) ((EHdr (sz := sz)V1)[64--24]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse14 =>
      {| st_op :=
          extract(Scratch32) ;;
          V1 <- EConcat (m := 32) (EHdr (sz := sz)Scratch32) ((EHdr (sz := sz)V1)[64--32]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse15 =>
      {| st_op :=
          extract(Scratch40) ;;
          V1 <- EConcat (m := 24) (EHdr (sz := sz)Scratch40) ((EHdr (sz := sz)V1)[64--40]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse16 =>
      {| st_op :=
          extract(Scratch48) ;;
          V1 <- EConcat (m := 16) (EHdr (sz := sz)Scratch48) ((EHdr (sz := sz)V1)[64--48]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse17 =>
      {| st_op :=
          extract(Scratch56) ;;
          V1 <- EConcat (m := 8) (EHdr (sz := sz)Scratch56) ((EHdr (sz := sz)V1)[64--56]) ;
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
         st_trans := transition select (| EHdr (sz := sz)T2, EHdr (sz := sz)L2 |) {{
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
          V1 <- EConcat (m := 56) (EHdr (sz := sz)Scratch8) ((EHdr (sz := sz)V2)[64--8]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse22 =>
      {| st_op :=
          extract(Scratch16) ;;
          V2 <- EConcat (m := 48) (EHdr (sz := sz)Scratch16) ((EHdr (sz := sz)V2)[64--16]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse23 =>
      {| st_op :=
          extract(Scratch24) ;;
          V2 <- EConcat (m := 40) (EHdr (sz := sz)Scratch24) ((EHdr (sz := sz)V2)[64--24]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse24 =>
      {| st_op :=
          extract(Scratch32) ;;
          V2 <- EConcat (m := 32) (EHdr (sz := sz)Scratch32) ((EHdr (sz := sz)V2)[64--32]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse25 =>
      {| st_op :=
          extract(Scratch40) ;;
          V2 <- EConcat (m := 24) (EHdr (sz := sz)Scratch40) ((EHdr (sz := sz)V2)[64--40]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse26 =>
      {| st_op :=
          extract(Scratch48) ;;
          V2 <- EConcat (m := 16) (EHdr (sz := sz)Scratch48) ((EHdr (sz := sz)V2)[64--48]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse27 =>
      {| st_op :=
          extract(Scratch56) ;;
          V2 <- EConcat (m := 8) (EHdr (sz := sz)Scratch56) ((EHdr (sz := sz)V2)[64--56]) ;
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
         st_trans := transition select (| EHdr (sz := sz)T3, EHdr (sz := sz)L3 |) {{
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
          V3 <- EConcat (m := 56) (EHdr (sz := sz)Scratch8) ((EHdr (sz := sz)V3)[64--8]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse32 =>
      {| st_op :=
          extract(Scratch16) ;;
          V3 <- EConcat (m := 48) (EHdr (sz := sz)Scratch16) ((EHdr (sz := sz)V3)[64--16]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse33 =>
      {| st_op :=
          extract(Scratch24) ;;
          V3 <- EConcat (m := 40) (EHdr (sz := sz)Scratch24) ((EHdr (sz := sz)V3)[64--24]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse34 =>
      {| st_op :=
          extract(Scratch32) ;;
          V3 <- EConcat (m := 32) (EHdr (sz := sz)Scratch32) ((EHdr (sz := sz)V3)[64--32]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse35 =>
      {| st_op :=
          extract(Scratch40) ;;
          V3 <- EConcat (m := 24) (EHdr (sz := sz)Scratch40) ((EHdr (sz := sz)V3)[64--40]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse36 =>
      {| st_op :=
          extract(Scratch48) ;;
          V3 <- EConcat (m := 16) (EHdr (sz := sz)Scratch48) ((EHdr (sz := sz)V3)[64--48]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse37 =>
      {| st_op :=
          extract(Scratch56) ;;
          V3 <- EConcat (m := 8) (EHdr (sz := sz)Scratch56) ((EHdr (sz := sz)V3)[64--56]) ;
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
         st_trans := transition select (| EHdr (sz := sz)T4, EHdr (sz := sz)L4 |) {{
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
          V4 <- EConcat (m := 56) (EHdr (sz := sz)Scratch8) ((EHdr (sz := sz)V4)[64--8]) ;
         st_trans := transition inl Parse5;
      |}
    | Parse42 =>
      {| st_op :=
          extract(Scratch16) ;;
          V4 <- EConcat (m := 48) (EHdr (sz := sz)Scratch16) ((EHdr (sz := sz)V4)[64--16]) ;
         st_trans := transition inl Parse5;
      |}
    | Parse43 =>
      {| st_op :=
          extract(Scratch24) ;;
          V4 <- EConcat (m := 40) (EHdr (sz := sz)Scratch24) ((EHdr (sz := sz)V4)[64--24]) ;
         st_trans := transition inl Parse5;
      |}
    | Parse44 =>
      {| st_op :=
          extract(Scratch32) ;;
          V4 <- EConcat (m := 32) (EHdr (sz := sz)Scratch32) ((EHdr (sz := sz)V4)[64--32]) ;
         st_trans := transition inl Parse5;
      |}
    | Parse45 =>
      {| st_op :=
          extract(Scratch40) ;;
          V4 <- EConcat (m := 24) (EHdr (sz := sz)Scratch40) ((EHdr (sz := sz)V4)[64--40]) ;
         st_trans := transition inl Parse5;
      |}
    | Parse46 =>
      {| st_op :=
          extract(Scratch48) ;;
          V4 <- EConcat (m := 16) (EHdr (sz := sz)Scratch48) ((EHdr (sz := sz)V4)[64--48]) ;
         st_trans := transition inl Parse5;
      |}
    | Parse47 =>
      {| st_op :=
          extract(Scratch56) ;;
          V4 <- EConcat (m := 8) (EHdr (sz := sz)Scratch56) ((EHdr (sz := sz)V4)[64--56]) ;
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
         st_trans := transition select (| EHdr (sz := sz)T5, EHdr (sz := sz)L5 |) {{
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
          V5 <- EConcat (m := 56) (EHdr (sz := sz)Scratch8) ((EHdr (sz := sz)V5)[64--8]) ;
         st_trans := transition inl Parse6;
      |}
    | Parse52 =>
      {| st_op :=
          extract(Scratch16) ;;
          V5 <- EConcat (m := 48) (EHdr (sz := sz)Scratch16) ((EHdr (sz := sz)V5)[64--16]) ;
         st_trans := transition inl Parse6;
      |}
    | Parse53 =>
      {| st_op :=
          extract(Scratch24) ;;
          V5 <- EConcat (m := 40) (EHdr (sz := sz)Scratch24) ((EHdr (sz := sz)V5)[64--24]) ;
         st_trans := transition inl Parse6;
      |}
    | Parse54 =>
      {| st_op :=
          extract(Scratch32) ;;
          V5 <- EConcat (m := 32) (EHdr (sz := sz)Scratch32) ((EHdr (sz := sz)V5)[64--32]) ;
         st_trans := transition inl Parse6;
      |}
    | Parse55 =>
      {| st_op :=
          extract(Scratch40) ;;
          V5 <- EConcat (m := 24) (EHdr (sz := sz)Scratch40) ((EHdr (sz := sz)V5)[64--40]) ;
         st_trans := transition inl Parse6;
      |}
    | Parse56 =>
      {| st_op :=
          extract(Scratch48) ;;
          V5 <- EConcat (m := 16) (EHdr (sz := sz)Scratch48) ((EHdr (sz := sz)V5)[64--48]) ;
         st_trans := transition inl Parse6;
      |}
    | Parse57 =>
      {| st_op :=
          extract(Scratch56) ;;
          V5 <- EConcat (m := 8) (EHdr (sz := sz)Scratch56) ((EHdr (sz := sz)V5)[64--56]) ;
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
         st_trans := transition select (| EHdr (sz := sz)T6, EHdr (sz := sz)L6 |) {{
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
          V6 <- EConcat (m := 56) (EHdr (sz := sz)Scratch8) ((EHdr (sz := sz)V6)[64--8]) ;
         st_trans := transition inl Parse7;
      |}
    | Parse62 =>
      {| st_op :=
          extract(Scratch16) ;;
          V6 <- EConcat (m := 48) (EHdr (sz := sz)Scratch16) ((EHdr (sz := sz)V6)[64--16]) ;
         st_trans := transition inl Parse7;
      |}
    | Parse63 =>
      {| st_op :=
          extract(Scratch24) ;;
          V6 <- EConcat (m := 40) (EHdr (sz := sz)Scratch24) ((EHdr (sz := sz)V6)[64--24]) ;
         st_trans := transition inl Parse7;
      |}
    | Parse64 =>
      {| st_op :=
          extract(Scratch32) ;;
          V6 <- EConcat (m := 32) (EHdr (sz := sz)Scratch32) ((EHdr (sz := sz)V6)[64--32]) ;
         st_trans := transition inl Parse7;
      |}
    | Parse65 =>
      {| st_op :=
          extract(Scratch40) ;;
          V6 <- EConcat (m := 24) (EHdr (sz := sz)Scratch40) ((EHdr (sz := sz)V6)[64--40]) ;
         st_trans := transition inl Parse7;
      |}
    | Parse66 =>
      {| st_op :=
          extract(Scratch48) ;;
          V6 <- EConcat (m := 16) (EHdr (sz := sz)Scratch48) ((EHdr (sz := sz)V6)[64--48]) ;
         st_trans := transition inl Parse7;
      |}
    | Parse67 =>
      {| st_op :=
          extract(Scratch56) ;;
          V6 <- EConcat (m := 8) (EHdr (sz := sz)Scratch56) ((EHdr (sz := sz)V6)[64--56]) ;
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
         st_trans := transition select (| EHdr (sz := sz)T7, EHdr (sz := sz)L7 |) {{
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
          V7 <- EConcat (m := 56) (EHdr (sz := sz)Scratch8) ((EHdr (sz := sz)V7)[64--8]) ;
         st_trans := transition inl Parse8;
      |}
    | Parse72 =>
      {| st_op :=
          extract(Scratch16) ;;
          V7 <- EConcat (m := 48) (EHdr (sz := sz)Scratch16) ((EHdr (sz := sz)V7)[64--16]) ;
         st_trans := transition inl Parse8;
      |}
    | Parse73 =>
      {| st_op :=
          extract(Scratch24) ;;
          V7 <- EConcat (m := 40) (EHdr (sz := sz)Scratch24) ((EHdr (sz := sz)V7)[64--24]) ;
         st_trans := transition inl Parse8;
      |}
    | Parse74 =>
      {| st_op :=
          extract(Scratch32) ;;
          V7 <- EConcat (m := 32) (EHdr (sz := sz)Scratch32) ((EHdr (sz := sz)V7)[64--32]) ;
         st_trans := transition inl Parse8;
      |}
    | Parse75 =>
      {| st_op :=
          extract(Scratch40) ;;
          V7 <- EConcat (m := 24) (EHdr (sz := sz)Scratch40) ((EHdr (sz := sz)V7)[64--40]) ;
         st_trans := transition inl Parse8;
      |}
    | Parse76 =>
      {| st_op :=
          extract(Scratch48) ;;
          V7 <- EConcat (m := 16) (EHdr (sz := sz)Scratch48) ((EHdr (sz := sz)V7)[64--48]) ;
         st_trans := transition inl Parse8;
      |}
    | Parse77 =>
      {| st_op :=
          extract(Scratch56) ;;
          V7 <- EConcat (m := 8) (EHdr (sz := sz)Scratch56) ((EHdr (sz := sz)V7)[64--56]) ;
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
         st_trans := transition select (| EHdr (sz := sz)T8, EHdr (sz := sz)L8 |) {{
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
          V8 <- EConcat (m := 56) (EHdr (sz := sz)Scratch8) ((EHdr (sz := sz)V8)[64--8]) ;
         st_trans := transition inl Parse9;
      |}
    | Parse82 =>
      {| st_op :=
          extract(Scratch16) ;;
          V8 <- EConcat (m := 48) (EHdr (sz := sz)Scratch16) ((EHdr (sz := sz)V8)[64--16]) ;
         st_trans := transition inl Parse9;
      |}
    | Parse83 =>
      {| st_op :=
          extract(Scratch24) ;;
          V8 <- EConcat (m := 40) (EHdr (sz := sz)Scratch24) ((EHdr (sz := sz)V8)[64--24]) ;
         st_trans := transition inl Parse9;
      |}
    | Parse84 =>
      {| st_op :=
          extract(Scratch32) ;;
          V8 <- EConcat (m := 32) (EHdr (sz := sz)Scratch32) ((EHdr (sz := sz)V8)[64--32]) ;
         st_trans := transition inl Parse9;
      |}
    | Parse85 =>
      {| st_op :=
          extract(Scratch40) ;;
          V8 <- EConcat (m := 24) (EHdr (sz := sz)Scratch40) ((EHdr (sz := sz)V8)[64--40]) ;
         st_trans := transition inl Parse9;
      |}
    | Parse86 =>
      {| st_op :=
          extract(Scratch48) ;;
          V8 <- EConcat (m := 16) (EHdr (sz := sz)Scratch48) ((EHdr (sz := sz)V8)[64--48]) ;
         st_trans := transition inl Parse9;
      |}
    | Parse87 =>
      {| st_op :=
          extract(Scratch56) ;;
          V8 <- EConcat (m := 8) (EHdr (sz := sz)Scratch56) ((EHdr (sz := sz)V8)[64--56]) ;
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
         st_trans := transition select (| EHdr (sz := sz)T9, EHdr (sz := sz)L9 |) {{
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
          V9 <- EConcat (m := 56) (EHdr (sz := sz)Scratch8) ((EHdr (sz := sz)V9)[64--8]) ;
         st_trans := transition accept;
      |}
    | Parse92 =>
      {| st_op :=
          extract(Scratch16) ;;
          V9 <- EConcat (m := 48) (EHdr (sz := sz)Scratch16) ((EHdr (sz := sz)V9)[64--16]) ;
         st_trans := transition accept;
      |}
    | Parse93 =>
      {| st_op :=
          extract(Scratch24) ;;
          V9 <- EConcat (m := 40) (EHdr (sz := sz)Scratch24) ((EHdr (sz := sz)V9)[64--24]) ;
         st_trans := transition accept;
      |}
    | Parse94 =>
      {| st_op :=
          extract(Scratch32) ;;
          V9 <- EConcat (m := 32) (EHdr (sz := sz)Scratch32) ((EHdr (sz := sz)V9)[64--32]) ;
         st_trans := transition accept;
      |}
    | Parse95 =>
      {| st_op :=
          extract(Scratch40) ;;
          V9 <- EConcat (m := 24) (EHdr (sz := sz)Scratch40) ((EHdr (sz := sz)V9)[64--40]) ;
         st_trans := transition accept;
      |}
    | Parse96 =>
      {| st_op :=
          extract(Scratch48) ;;
          V9 <- EConcat (m := 16) (EHdr (sz := sz)Scratch48) ((EHdr (sz := sz)V9)[64--48]) ;
         st_trans := transition accept;
      |}
    | Parse97 =>
      {| st_op :=
          extract(Scratch56) ;;
          V9 <- EConcat (m := 8) (EHdr (sz := sz)Scratch56) ((EHdr (sz := sz)V9)[64--56]) ;
         st_trans := transition accept;
      |}
    | Parse98 =>
      {| st_op :=
          extract(V9) ;
         st_trans := transition accept;
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).

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
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Scratch8
  | Scratch16
  | Scratch24
  | Scratch32
  | Scratch40
  | Scratch48
  | Scratch56
  | T0
  | L0
  | V0
  | T1
  | L1
  | V1
  | T2
  | L2
  | V2
  | T3
  | L3
  | V3
  | T4
  | L4
  | V4.

  Definition sz (h: header) : nat :=
    match h with
    | Scratch8 => 8
    | Scratch16 => 16
    | Scratch24 => 24
    | Scratch32 => 32
    | Scratch40 => 40
    | Scratch48 => 48
    | Scratch56 => 56
    | T0 | L0
    | T1 | L1
    | T2 | L2
    | T3 | L3
    | T4 | L4 => 8
    | V0
    | V1
    | V2
    | V3
    | V4 => 64
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) :=
    match s with
    | Parse0 =>
      {| st_op :=
          extract(T0) ;;
          extract(L0) ;
         st_trans := transition select (| EHdr (sz := sz) T0, EHdr (sz := sz) L0 |) {{
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
          V0 <- EConcat (m := 56) (EHdr (sz := sz) Scratch8) ((EHdr (sz := sz) V0)[64--8]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse02 =>
      {| st_op :=
          extract(Scratch16) ;;
          V0 <- EConcat (m := 48) (EHdr (sz := sz) Scratch16) ((EHdr (sz := sz) V0)[64--16]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse03 =>
      {| st_op :=
          extract(Scratch24) ;;
          V0 <- EConcat (m := 40) (EHdr (sz := sz) Scratch24) ((EHdr (sz := sz) V0)[64--24]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse04 =>
      {| st_op :=
          extract(Scratch32) ;;
          V0 <- EConcat (m := 32) (EHdr (sz := sz) Scratch32) ((EHdr (sz := sz) V0)[64--32]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse05 =>
      {| st_op :=
          extract(Scratch40) ;;
          V0 <- EConcat (m := 24) (EHdr (sz := sz) Scratch40) ((EHdr (sz := sz) V0)[64--40]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse06 =>
      {| st_op :=
          extract(Scratch48) ;;
          V0 <- EConcat (m := 16) (EHdr (sz := sz) Scratch48) ((EHdr (sz := sz) V0)[64--48]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse07 =>
      {| st_op :=
          extract(Scratch56) ;;
          V0 <- EConcat (m := 8) (EHdr (sz := sz) Scratch56) ((EHdr (sz := sz) V0)[64--56]) ;
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
         st_trans := transition select (| EHdr (sz := sz) T1, EHdr (sz := sz) L1 |) {{
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
          V1 <- EConcat (m := 56) (EHdr (sz := sz) Scratch8) ((EHdr (sz := sz) V1)[64--8]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse12 =>
      {| st_op :=
          extract(Scratch16) ;;
          V1 <- EConcat (m := 48) (EHdr (sz := sz) Scratch16) ((EHdr (sz := sz) V1)[64--16]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse13 =>
      {| st_op :=
          extract(Scratch24) ;;
          V1 <- EConcat (m := 40) (EHdr (sz := sz) Scratch24) ((EHdr (sz := sz) V1)[64--24]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse14 =>
      {| st_op :=
          extract(Scratch32) ;;
          V1 <- EConcat (m := 32) (EHdr (sz := sz) Scratch32) ((EHdr (sz := sz) V1)[64--32]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse15 =>
      {| st_op :=
          extract(Scratch40) ;;
          V1 <- EConcat (m := 24) (EHdr (sz := sz) Scratch40) ((EHdr (sz := sz) V1)[64--40]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse16 =>
      {| st_op :=
          extract(Scratch48) ;;
          V1 <- EConcat (m := 16) (EHdr (sz := sz) Scratch48) ((EHdr (sz := sz) V1)[64--48]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse17 =>
      {| st_op :=
          extract(Scratch56) ;;
          V1 <- EConcat (m := 8) (EHdr (sz := sz) Scratch56) ((EHdr (sz := sz) V1)[64--56]) ;
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
         st_trans := transition select (| EHdr (sz := sz) T2, EHdr (sz := sz) L2 |) {{
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
          V1 <- EConcat (m := 56) (EHdr (sz := sz) Scratch8) ((EHdr (sz := sz) V2)[64--8]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse22 =>
      {| st_op :=
          extract(Scratch16) ;;
          V2 <- EConcat (m := 48) (EHdr (sz := sz) Scratch16) ((EHdr (sz := sz) V2)[64--16]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse23 =>
      {| st_op :=
          extract(Scratch24) ;;
          V2 <- EConcat (m := 40) (EHdr (sz := sz) Scratch24) ((EHdr (sz := sz) V2)[64--24]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse24 =>
      {| st_op :=
          extract(Scratch32) ;;
          V2 <- EConcat (m := 32) (EHdr (sz := sz) Scratch32) ((EHdr (sz := sz) V2)[64--32]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse25 =>
      {| st_op :=
          extract(Scratch40) ;;
          V2 <- EConcat (m := 24) (EHdr (sz := sz) Scratch40) ((EHdr (sz := sz) V2)[64--40]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse26 =>
      {| st_op :=
          extract(Scratch48) ;;
          V2 <- EConcat (m := 16) (EHdr (sz := sz) Scratch48) ((EHdr (sz := sz) V2)[64--48]) ;
         st_trans := transition inl Parse3;
      |}
    | Parse27 =>
      {| st_op :=
          extract(Scratch56) ;;
          V2 <- EConcat (m := 8) (EHdr (sz := sz) Scratch56) ((EHdr (sz := sz) V2)[64--56]) ;
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
         st_trans := transition select (| EHdr (sz := sz) T3, EHdr (sz := sz) L3 |) {{
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
          V3 <- EConcat (m := 56) (EHdr (sz := sz) Scratch8) ((EHdr (sz := sz) V3)[64--8]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse32 =>
      {| st_op :=
          extract(Scratch16) ;;
          V3 <- EConcat (m := 48) (EHdr (sz := sz) Scratch16) ((EHdr (sz := sz) V3)[64--16]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse33 =>
      {| st_op :=
          extract(Scratch24) ;;
          V3 <- EConcat (m := 40) (EHdr (sz := sz) Scratch24) ((EHdr (sz := sz) V3)[64--24]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse34 =>
      {| st_op :=
          extract(Scratch32) ;;
          V3 <- EConcat (m := 32) (EHdr (sz := sz) Scratch32) ((EHdr (sz := sz) V3)[64--32]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse35 =>
      {| st_op :=
          extract(Scratch40) ;;
          V3 <- EConcat (m := 24) (EHdr (sz := sz) Scratch40) ((EHdr (sz := sz) V3)[64--40]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse36 =>
      {| st_op :=
          extract(Scratch48) ;;
          V3 <- EConcat (m := 16) (EHdr (sz := sz) Scratch48) ((EHdr (sz := sz) V3)[64--48]) ;
         st_trans := transition inl Parse4;
      |}
    | Parse37 =>
      {| st_op :=
          extract(Scratch56) ;;
          V3 <- EConcat (m := 8) (EHdr (sz := sz) Scratch56) ((EHdr (sz := sz) V3)[64--56]) ;
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
         st_trans := transition select (| EHdr (sz := sz) T4, EHdr (sz := sz) L4 |) {{
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
          V4 <- EConcat (m := 56) (EHdr (sz := sz) Scratch8) ((EHdr (sz := sz) V4)[64--8]) ;
         st_trans := transition accept;
      |}
    | Parse42 =>
      {| st_op :=
          extract(Scratch16) ;;
          V4 <- EConcat (m := 48) (EHdr (sz := sz) Scratch16) ((EHdr (sz := sz) V4)[64--16]) ;
         st_trans := transition accept;
      |}
    | Parse43 =>
      {| st_op :=
          extract(Scratch24) ;;
          V4 <- EConcat (m := 40) (EHdr (sz := sz) Scratch24) ((EHdr (sz := sz) V4)[64--24]) ;
         st_trans := transition accept;
      |}
    | Parse44 =>
      {| st_op :=
          extract(Scratch32) ;;
          V4 <- EConcat (m := 32) (EHdr (sz := sz) Scratch32) ((EHdr (sz := sz) V4)[64--32]) ;
         st_trans := transition accept;
      |}
    | Parse45 =>
      {| st_op :=
          extract(Scratch40) ;;
          V4 <- EConcat (m := 24) (EHdr (sz := sz) Scratch40) ((EHdr (sz := sz) V4)[64--40]) ;
         st_trans := transition accept;
      |}
    | Parse46 =>
      {| st_op :=
          extract(Scratch48) ;;
          V4 <- EConcat (m := 16) (EHdr (sz := sz) Scratch48) ((EHdr (sz := sz) V4)[64--48]) ;
         st_trans := transition accept;
      |}
    | Parse47 =>
      {| st_op :=
          extract(Scratch56) ;;
          V4 <- EConcat (m := 8) (EHdr (sz := sz) Scratch56) ((EHdr (sz := sz) V4)[64--56]) ;
         st_trans := transition accept;
      |}
    | Parse48 =>
      {| st_op :=
          extract(V4) ;
         st_trans := transition accept;
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).

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
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Scratch8
  | Scratch16
  | Scratch24
  | Scratch32
  | Scratch40
  | Scratch48
  | Scratch56
  | T0
  | L0
  | V0
  | T1
  | L1
  | V1.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition sz (h: header) : nat :=
    match h with
    | Scratch8 => 8
    | Scratch16 => 16
    | Scratch24 => 24
    | Scratch32 => 32
    | Scratch40 => 40
    | Scratch48 => 48
    | Scratch56 => 56
    | T0 | L0
    | T1 | L1 => 8
    | V0
    | V1 => 64
    end.

  Definition states (s: state) :=
    match s with
    | Parse0 =>
      {| st_op :=
          extract(T0) ;;
          extract(L0) ;
         st_trans := transition select (| EHdr (sz := sz) T0, EHdr (sz := sz) L0 |) {{
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
          V0 <- EConcat (m := 56) (EHdr (sz := sz) Scratch8) ((EHdr (sz := sz) V0)[64--8]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse02 =>
      {| st_op :=
          extract(Scratch16) ;;
          V0 <- EConcat (m := 48) (EHdr (sz := sz) Scratch16) ((EHdr (sz := sz) V0)[64--16]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse03 =>
      {| st_op :=
          extract(Scratch24) ;;
          V0 <- EConcat (m := 40) (EHdr (sz := sz) Scratch24) ((EHdr (sz := sz) V0)[64--24]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse04 =>
      {| st_op :=
          extract(Scratch32) ;;
          V0 <- EConcat (m := 32) (EHdr (sz := sz) Scratch32) ((EHdr (sz := sz) V0)[64--32]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse05 =>
      {| st_op :=
          extract(Scratch40) ;;
          V0 <- EConcat (m := 24) (EHdr (sz := sz) Scratch40) ((EHdr (sz := sz) V0)[64--40]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse06 =>
      {| st_op :=
          extract(Scratch48) ;;
          V0 <- EConcat (m := 16) (EHdr (sz := sz) Scratch48) ((EHdr (sz := sz) V0)[64--48]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse07 =>
      {| st_op :=
          extract(Scratch56) ;;
          V0 <- EConcat (m := 8) (EHdr (sz := sz) Scratch56) ((EHdr (sz := sz) V0)[64--56]) ;
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
         st_trans := transition select (| EHdr (sz := sz) T1, EHdr (sz := sz) L1 |) {{
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
          V1 <- EConcat (m := 56) (EHdr (sz := sz) Scratch8) ((EHdr (sz := sz) V1)[64--8]) ;
         st_trans := transition accept;
      |}
    | Parse12 =>
      {| st_op :=
          extract(Scratch16) ;;
          V1 <- EConcat (m := 48) (EHdr (sz := sz) Scratch16) ((EHdr (sz := sz) V1)[64--16]) ;
         st_trans := transition accept;
      |}
    | Parse13 =>
      {| st_op :=
          extract(Scratch24) ;;
          V1 <- EConcat (m := 40) (EHdr (sz := sz) Scratch24) ((EHdr (sz := sz) V1)[64--24]) ;
         st_trans := transition accept;
      |}
    | Parse14 =>
      {| st_op :=
          extract(Scratch32) ;;
          V1 <- EConcat (m := 32) (EHdr (sz := sz) Scratch32) ((EHdr (sz := sz) V1)[64--32]) ;
         st_trans := transition accept;
      |}
    | Parse15 =>
      {| st_op :=
          extract(Scratch40) ;;
          V1 <- EConcat (m := 24) (EHdr (sz := sz) Scratch40) ((EHdr (sz := sz) V1)[64--40]) ;
         st_trans := transition accept;
      |}
    | Parse16 =>
      {| st_op :=
          extract(Scratch48) ;;
          V1 <- EConcat (m := 16) (EHdr (sz := sz) Scratch48) ((EHdr (sz := sz) V1)[64--48]) ;
         st_trans := transition accept;
      |}
    | Parse17 =>
      {| st_op :=
          extract(Scratch56) ;;
          V1 <- EConcat (m := 8) (EHdr (sz := sz) Scratch56) ((EHdr (sz := sz) V1)[64--56]) ;
         st_trans := transition accept;
      |}
    | Parse18 =>
      {| st_op :=
          extract(V1) ;
         st_trans := transition accept;
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).

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
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Scratch8
  | Scratch16
  | T0
  | L0
  | V0
  | T1
  | L1
  | V1.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition sz (h: header) : nat :=
    match h with
    | Scratch8 => 8
    | Scratch16 => 16
    | T0 | L0
    | T1 | L1 => 8
    | V0
    | V1 => 24
    end.

  Definition states (s: state) :=
    match s with
    | Parse0 =>
      {| st_op :=
          extract(T0) ;;
          extract(L0) ;
         st_trans := transition select (| EHdr (sz := sz) T0, EHdr (sz := sz) L0 |) {{
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
          V0 <- EConcat (m := 16) (EHdr (sz := sz) Scratch8) ((EHdr (sz := sz) V0)[24--8]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse02 =>
      {| st_op :=
          extract(Scratch16) ;;
          V0 <- EConcat (m := 8) (EHdr (sz := sz) Scratch16) ((EHdr (sz := sz) V0)[24--16]) ;
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
         st_trans := transition select (| EHdr (sz := sz) T1, EHdr (sz := sz) L1 |) {{
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
          V1 <- EConcat (m := 16) (EHdr (sz := sz) Scratch8) ((EHdr (sz := sz) V1)[24--8]) ;
         st_trans := transition accept;
      |}
    | Parse12 =>
      {| st_op :=
          extract(Scratch16) ;;
          V1 <- EConcat (m := 8) (EHdr (sz := sz) Scratch16) ((EHdr (sz := sz) V1)[24--16]) ;
         st_trans := transition accept;
      |}
    | Parse13 =>
      {| st_op :=
          extract(V1) ;
         st_trans := transition accept;
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).

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
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Scratch8
  | Scratch16
  | Scratch24
  | T0
  | L0
  | T1
  | L1
  | V.

  Definition sz (h: header) : nat :=
    match h with
    | Scratch8 => 8
    | Scratch16 => 16
    | Scratch24 => 24
    | T0 | L0
    | T1 | L1 => 8
    | V => 16
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) :=
    match s with
    | Parse0 =>
      {| st_op :=
          extract(T0) ;;
          extract(L0) ;
         st_trans := transition select (| EHdr (sz := sz) T0, EHdr (sz := sz) L0 |) {{
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
         st_trans := transition select (| EHdr (sz := sz) T1, EHdr (sz := sz) L1 |) {{
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

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).

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
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Scratch8
  | Scratch16
  | Scratch24
  | Scratch32
  | Scratch40
  | T0
  | L0
  | V0
  | T1
  | L1
  | V1.

  Definition sz (h: header) : nat :=
    match h with
    | Scratch8 => 8
    | Scratch16 => 16
    | Scratch24 => 24
    | Scratch32 => 32
    | Scratch40 => 40
    | T0 | L0
    | T1 | L1 => 8
    | V0
    | V1 => 48
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) :=
    match s with
    | Parse0 =>
      {| st_op :=
          extract(T0) ;;
          extract(L0) ;
         st_trans := transition select (| EHdr (sz := sz) T0, EHdr (sz := sz) L0 |) {{
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
          V0 <- EConcat (m := 40) (EHdr (sz := sz) Scratch8) ((EHdr (sz := sz) V0)[48--8]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse02 =>
      {| st_op :=
          extract(Scratch16) ;;
          V0 <- EConcat (m := 32) (EHdr (sz := sz) Scratch16) ((EHdr (sz := sz) V0)[48--16]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse03 =>
      {| st_op :=
          extract(Scratch24) ;;
          V0 <- EConcat (m := 24) (EHdr (sz := sz) Scratch24) ((EHdr (sz := sz) V0)[48--24]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse04 =>
      {| st_op :=
          extract(Scratch32) ;;
          V0 <- EConcat (m := 16) (EHdr (sz := sz) Scratch32) ((EHdr (sz := sz) V0)[48--32]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse05 =>
      {| st_op :=
          extract(Scratch40) ;;
          V0 <- EConcat (m := 8) (EHdr (sz := sz) Scratch40) ((EHdr (sz := sz) V0)[48--40]) ;
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
         st_trans := transition select (| EHdr (sz := sz) T1, EHdr (sz := sz) L1 |) {{
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
          V1 <- EConcat (m := 40) (EHdr (sz := sz) Scratch8) ((EHdr (sz := sz) V1)[48--8]) ;
         st_trans := transition accept;
      |}
    | Parse12 =>
      {| st_op :=
          extract(Scratch16) ;;
          V1 <- EConcat (m := 32) (EHdr (sz := sz) Scratch16) ((EHdr (sz := sz) V1)[48--16]) ;
         st_trans := transition accept;
      |}
    | Parse13 =>
      {| st_op :=
          extract(Scratch24) ;;
          V1 <- EConcat (m := 24) (EHdr (sz := sz) Scratch24) ((EHdr (sz := sz) V1)[48--24]) ;
         st_trans := transition accept;
      |}
    | Parse14 =>
      {| st_op :=
          extract(Scratch32) ;;
          V1 <- EConcat (m := 16) (EHdr (sz := sz) Scratch32) ((EHdr (sz := sz) V1)[48--32]) ;
         st_trans := transition accept;
      |}
    | Parse15 =>
      {| st_op :=
          extract(Scratch40) ;;
          V1 <- EConcat (m := 8) (EHdr (sz := sz) Scratch40) ((EHdr (sz := sz) V1)[48--40]) ;
         st_trans := transition accept;
      |}
    | Parse16 =>
      {| st_op :=
          extract(V1) ;
         st_trans := transition accept;
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).

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
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Scratch8
  | Scratch16
  | Scratch24
  | Scratch32
  | Scratch40
  | T0
  | L0
  | V0
  | T1
  | L1
  | V1
  | T2
  | L2
  | V2.

  Definition sz (h: header) : nat :=
    match h with
    | Scratch8 => 8
    | Scratch16 => 16
    | Scratch24 => 24
    | Scratch32 => 32
    | Scratch40 => 40
    | T0 | L0
    | T1 | L1
    | T2 | L2 => 8
    | V0
    | V1
    | V2 => 48
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) :=
    match s with
    | Parse0 =>
      {| st_op :=
          extract(T0) ;;
          extract(L0) ;
         st_trans := transition select (| EHdr (sz := sz) T0, EHdr (sz := sz) L0 |) {{
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
          V0 <- EConcat (m := 40) (EHdr (sz := sz) Scratch8) ((EHdr (sz := sz) V0)[48--8]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse02 =>
      {| st_op :=
          extract(Scratch16) ;;
          V0 <- EConcat (m := 32) (EHdr (sz := sz) Scratch16) ((EHdr (sz := sz) V0)[48--16]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse03 =>
      {| st_op :=
          extract(Scratch24) ;;
          V0 <- EConcat (m := 24) (EHdr (sz := sz) Scratch24) ((EHdr (sz := sz) V0)[48--24]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse04 =>
      {| st_op :=
          extract(Scratch32) ;;
          V0 <- EConcat (m := 16) (EHdr (sz := sz) Scratch32) ((EHdr (sz := sz) V0)[48--32]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse05 =>
      {| st_op :=
          extract(Scratch40) ;;
          V0 <- EConcat (m := 8) (EHdr (sz := sz) Scratch40) ((EHdr (sz := sz) V0)[48--40]) ;
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
         st_trans := transition select (| EHdr (sz := sz) T1, EHdr (sz := sz) L1 |) {{
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
          V1 <- EConcat (m := 40) (EHdr (sz := sz) Scratch8) ((EHdr (sz := sz) V1)[48--8]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse12 =>
      {| st_op :=
          extract(Scratch16) ;;
          V1 <- EConcat (m := 32) (EHdr (sz := sz) Scratch16) ((EHdr (sz := sz) V1)[48--16]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse13 =>
      {| st_op :=
          extract(Scratch24) ;;
          V1 <- EConcat (m := 24) (EHdr (sz := sz) Scratch24) ((EHdr (sz := sz) V1)[48--24]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse14 =>
      {| st_op :=
          extract(Scratch32) ;;
          V1 <- EConcat (m := 16) (EHdr (sz := sz) Scratch32) ((EHdr (sz := sz) V1)[48--32]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse15 =>
      {| st_op :=
          extract(Scratch40) ;;
          V1 <- EConcat (m := 8) (EHdr (sz := sz) Scratch40) ((EHdr (sz := sz) V1)[48--40]) ;
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
         st_trans := transition select (| EHdr (sz := sz) T2, EHdr (sz := sz) L2 |) {{
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
          V1 <- EConcat (m := 40) (EHdr (sz := sz) Scratch8) ((EHdr (sz := sz) V2)[48--8]) ;
         st_trans := transition accept;
      |}
    | Parse22 =>
      {| st_op :=
          extract(Scratch16) ;;
          V2 <- EConcat (m := 32) (EHdr (sz := sz) Scratch16) ((EHdr (sz := sz) V2)[48--16]) ;
         st_trans := transition accept;
      |}
    | Parse23 =>
      {| st_op :=
          extract(Scratch24) ;;
          V2 <- EConcat (m := 24) (EHdr (sz := sz) Scratch24) ((EHdr (sz := sz) V2)[48--24]) ;
         st_trans := transition accept;
      |}
    | Parse24 =>
      {| st_op :=
          extract(Scratch32) ;;
          V2 <- EConcat (m := 16) (EHdr (sz := sz) Scratch32) ((EHdr (sz := sz) V2)[48--32]) ;
         st_trans := transition accept;
      |}
    | Parse25 =>
      {| st_op :=
          extract(Scratch40) ;;
          V2 <- EConcat (m := 8) (EHdr (sz := sz) Scratch40) ((EHdr (sz := sz) V2)[48--40]) ;
         st_trans := transition accept;
      |}
    | Parse26 =>
      {| st_op :=
          extract(V2) ;
         st_trans := transition accept;
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).

End IPOptionsRef63.
