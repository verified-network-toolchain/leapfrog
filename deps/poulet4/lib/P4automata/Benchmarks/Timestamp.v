Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.Notations.

Require Import Poulet4.P4automata.BisimChecker.

Open Scope p4a.

Ltac prep_equiv :=
  unfold Equivalence.equiv, RelationClasses.complement in *;
  program_simpl; try congruence.

Obligation Tactic := prep_equiv.

Module TimestampRefSingle.
  Inductive state :=
  | Start
  | ParseValue1
  | ParseValue2
  | ParseValue3
  | ParseValue4
  | ParseValue5
  | ParseValue6.

  Scheme Equality for state.

  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [Start; ParseValue1; ParseValue2; ParseValue3; ParseValue4; ParseValue5; ParseValue6] |}.
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
  | Typ : header 8
  | Len : header 8
  | Value : header 48
  | Scratch8 : header 8
  | Scratch16 : header 16
  | Scratch24 : header 24
  | Scratch32 : header 32
  | Scratch40 : header 40.

  Derive Signature for header.

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
    | Value, Value => left eq_refl
    | _, _ => idProp
    end.

  Definition h8_eq_dec (x y: header 8) : {x = y} + {x <> y}. 
  refine (
    match x with 
    | Typ => 
      match y with 
      | Typ => left eq_refl
      | Len => right _
      | Scratch8 => right _
      end
    | Len => 
      match y with 
      | Typ => right _
      | Len => left eq_refl
      | Scratch8 => right _
      end
    | Scratch8 => 
        match y with 
        | Typ => right _
        | Len => right _
        | Scratch8 => left eq_refl
        end
    end
  ); unfold "<>"; intros H; inversion H.
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
    {| enum := [ 
      existT _ _ Len; existT _ _ Typ; existT _ _ Value;  
      existT _ _ Scratch8; existT _ _ Scratch16; existT _ _ Scratch24;
      existT _ _ Scratch32; existT _ _ Scratch40
      
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

  Definition states (s: state) :=
    match s with
    | Start =>
      {| st_op := 
          extract(Typ) ;;
          extract(Len) ;
        st_trans := transition select (| EHdr Len |) {{
          [| exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
          [| exact #b|0|0|0|0|0|0|0|1 |] ==> inl ParseValue1 ;;;
          [| exact #b|0|0|0|0|0|0|1|0 |] ==> inl ParseValue2 ;;;
          [| exact #b|0|0|0|0|0|0|1|1 |] ==> inl ParseValue3 ;;;
          [| exact #b|0|0|0|0|0|1|0|0 |] ==> inl ParseValue4 ;;;
          [| exact #b|0|0|0|0|0|1|0|1 |] ==> inl ParseValue5 ;;;
          [| exact #b|0|0|0|0|0|1|1|0 |] ==> inl ParseValue6 ;;;
            reject
        }}
      |}
    | ParseValue1 =>
      {| st_op := 
          extract(Scratch8) ;; 
          Value <- EConcat (m := 40) (EHdr Scratch8) ((EHdr Value)[48--8])  ;
        st_trans := transition accept
      |}
    | ParseValue2 =>
      {| st_op := 
          extract(Scratch16) ;; 
          Value <- EConcat (m := 32) (EHdr Scratch16) ((EHdr Value)[48--16])  ;
        st_trans := transition accept
      |}
    | ParseValue3 =>
      {| st_op := 
          extract(Scratch24) ;; 
          Value <- EConcat (m := 24) (EHdr Scratch24) ((EHdr Value)[48--24])  ;
        st_trans := transition accept
      |}
    | ParseValue4 =>
      {| st_op := 
          extract(Scratch32) ;; 
          Value <- EConcat (m := 16) (EHdr Scratch32) ((EHdr Value)[48--32])  ;
        st_trans := transition accept
      |}
    | ParseValue5 =>
      {| st_op := 
          extract(Scratch40) ;; 
          Value <- EConcat (m := 8) (EHdr Scratch40) ((EHdr Value)[48--40])  ;
        st_trans := transition accept
      |}
    | ParseValue6 =>
      {| st_op := extract(Value) ;
        st_trans := transition accept
      |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End TimestampRefSingle.


Module TimestampSpecSingle.
  Inductive state :=
  | Start
  | ParseValue1
  | ParseValue2
  | ParseValue3
  | ParseValue4
  | ParseValue5
  | ParseValue6
  | ParseTimestamp.

  Scheme Equality for state.

  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [Start; ParseValue1; ParseValue2; ParseValue3; ParseValue4; ParseValue5; ParseValue6; ParseTimestamp] |}.
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
  | Typ : header 8
  | Len : header 8
  | Scratch8 : header 8
  | Scratch16 : header 16
  | Scratch24 : header 24
  | Scratch32 : header 32
  | Scratch40 : header 40
  | Scratch48 : header 48
  | Pointer : header 8
  | Overflow: header 4
  | Flag: header 4
  | Timestamp: header 32.

  Derive Signature for header.

  Definition h4_eq_dec (x y: header 4) : {x = y} + {x <> y}.
  refine (
    match x, y with
    | Overflow, Flag => right _
    | Flag, Overflow => right _ 
    | Flag, Flag => left eq_refl
    | Overflow, Overflow => left eq_refl
    end
  ); unfold "<>"; intros H; inversion H.
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

  Definition h32_eq_dec (x y: header 32) : {x = y} + {x <> y}.
  refine (
    match x, y with
    | Scratch32, Timestamp => right _
    | Timestamp, Scratch32 => right _ 
    | Timestamp, Timestamp => left eq_refl
    | Scratch32, Scratch32 => left eq_refl
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.


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

  Definition h8_eq_dec (x y: header 8) : {x = y} + {x <> y}. 
  refine (
    match x with 
    | Typ => 
      match y with 
      | Typ => left eq_refl
      | Len => right _
      | Scratch8 => right _
      | Pointer => right _
      end
    | Len => 
      match y with 
      | Typ => right _
      | Len => left eq_refl
      | Scratch8 => right _
      | Pointer => right _
      end
    | Scratch8 => 
        match y with 
        | Typ => right _
        | Len => right _
        | Scratch8 => left eq_refl
        | Pointer => right _
        end
    | Pointer => 
      match y with 
      | Typ => right _
      | Len => right _
      | Scratch8 => right _
      | Pointer => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.


  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y 
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h8_eq_dec) :: 
        (existT _ _ h16_eq_dec) :: (existT _ _ h24_eq_dec) :: (existT _ _ h32_eq_dec) :: 
        (existT _ _ h40_eq_dec) :: (existT _ _ h48_eq_dec) :: (existT _ _ h4_eq_dec) :: nil).
  Defined. 

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [4; 8; 16; 24; 32; 40; 48].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ 
      existT _ _ Len; existT _ _ Typ;
      existT _ _ Scratch8; existT _ _ Scratch16; existT _ _ Scratch24;
      existT _ _ Scratch32; existT _ _ Scratch40; existT _ _ Scratch48;
      existT _ _ Overflow; existT _ _ Flag; existT _ _ Pointer; existT _ _ Timestamp
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

  Definition states (s: state) :=
    match s with
    | Start =>
      {| st_op := 
          extract(Typ) ;;
          extract(Len) ;
        st_trans := transition select (| EHdr Typ, EHdr Len |) {{
          [| exact #b|0|1|0|0|0|1|0|0, exact #b|0|0|0|0|0|1|1|0 |] ==> inl ParseTimestamp ;;;
          [| *, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
          [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl ParseValue1 ;;;
          [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl ParseValue2 ;;;
          [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl ParseValue3 ;;;
          [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl ParseValue4 ;;;
          [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl ParseValue5 ;;;
          [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl ParseValue6 ;;;
            reject
        }}
      |}
    | ParseTimestamp =>
      {| st_op := 
          extract(Pointer) ;;
          extract(Overflow) ;;
          extract(Flag) ;;
          extract(Timestamp) ;
        st_trans := transition accept (* TODO: validate pointer and flag? *)
      |}
    | ParseValue1 =>
      {| st_op := 
          extract(Scratch8) ;
        st_trans := transition accept
      |}
    | ParseValue2 =>
      {| st_op := 
          extract(Scratch16) ;
        st_trans := transition accept
      |}
    | ParseValue3 =>
      {| st_op := 
          extract(Scratch24) ;
        st_trans := transition accept
      |}
    | ParseValue4 =>
      {| st_op := 
          extract(Scratch32) ;
        st_trans := transition accept
      |}
    | ParseValue5 =>
      {| st_op := 
          extract(Scratch40) ;
        st_trans := transition accept
      |}
    | ParseValue6 =>
      {| st_op := extract(Scratch48) ;
        st_trans := transition accept
      |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End TimestampSpecSingle.


Module TimestampRefSmall.
  Inductive state :=
  | Start
  | Parse1
  | Parse2
  | Parse3.

  Scheme Equality for state.

  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [Start; Parse1; Parse2; Parse3] |}.
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
  | Len : header 2
  | Pref1 : header 8
  | Pref2: header 16
  | Timestamps : header 24.

  Derive Signature for header.

  Definition h2_eq_dec (x y: header 2) : {x = y} + {x <> y} :=
    match x, y with 
    | Len, Len => left eq_refl
    | _, _ => idProp
    end.

  Definition h8_eq_dec (x y: header 8) : {x = y} + {x <> y} :=
    match x, y with 
    | Pref1, Pref1 => left eq_refl
    | _, _ => idProp
    end.

  Definition h16_eq_dec (x y: header 16) : {x = y} + {x <> y} :=
    match x, y with 
    | Pref2, Pref2 => left eq_refl
    | _, _ => idProp
    end.

  Definition h24_eq_dec (x y: header 24) : {x = y} + {x <> y} :=
    match x, y with 
    | Timestamps, Timestamps => left eq_refl
    | _, _ => idProp
    end.

  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y 
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) 2 h2_eq_dec) :: 
        (existT _ 8 h8_eq_dec) :: (existT _ 16 h16_eq_dec) :: (existT _ 24 h24_eq_dec) :: nil).
  Defined. 

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [24; 16; 8; 2].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ Len; existT _ _ Pref1; existT _ _ Pref2;  existT _ _ Timestamps] |}.
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
    | Start =>
      {| st_op := 
          extract(Len) ;
         st_trans := transition select (| EHdr Len |) {{
           [| exact #b|0|0 |] ==> accept ;;;
           [| exact #b|0|1 |] ==> inl Parse1 ;;;
           [| exact #b|1|0 |] ==> inl Parse2 ;;;
           [| exact #b|1|1 |] ==> inl Parse3 ;;;
            reject
         }}
      |}
    | Parse1 =>
      {| st_op := 
          extract(Pref1) ;; 
          Timestamps <- EConcat (m := 16) (EHdr Pref1) ((EHdr Timestamps)[24--8])  ;
         st_trans := transition accept
      |}
    | Parse2 =>
      {| st_op := 
          extract(Pref2) ;; 
          Timestamps <- EConcat (m := 8) (EHdr Pref2) ((EHdr Timestamps)[24--16]) ;
         st_trans := transition accept
      |}
    | Parse3 =>
      {| st_op := extract(Timestamps) ;
         st_trans := transition accept
      |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End TimestampRefSmall.


Module TimestampSpecSmall.
  Inductive state :=
  | Start
  | Parse1
  | Parse2
  | Parse3.

  Scheme Equality for state.

  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [Start; Parse1; Parse2; Parse3] |}.
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
  | Len : header 2
  | T1 : header 8
  | T2 : header 8 
  | T3 : header 8.

  Derive Signature for header.

  Definition h2_eq_dec (x y: header 2) : {x = y} + {x <> y} :=
    match x, y with 
    | Len, Len => left eq_refl
    | _, _ => idProp
    end.

  Definition h8_eq_dec (x y: header 8) : {x = y} + {x <> y}.
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

  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y 
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) 2 h2_eq_dec) :: 
        (existT _ 8 h8_eq_dec) :: nil).
  Defined. 

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [8; 2].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ Len; existT _ _ T1; existT _ _ T2;  existT _ _ T3] |}.
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
    | Start =>
      {| st_op := 
          extract(Len) ;
         st_trans := transition select (| EHdr Len |) {{
           [| exact #b|0|0 |] ==> accept ;;;
           [| exact #b|0|1 |] ==> inl Parse1 ;;;
           [| exact #b|1|0 |] ==> inl Parse2 ;;;
           [| exact #b|1|1 |] ==> inl Parse3 ;;;
            reject
         }}
      |}
    | Parse1 =>
      {| st_op := 
          extract(T1) ;
         st_trans := transition accept
      |}
    | Parse2 =>
      {| st_op := 
          extract(T1) ;; 
          extract(T2) ;
         st_trans := transition accept
      |}
    | Parse3 =>
      {| st_op := 
          extract(T1) ;; 
          extract(T2) ;; 
          extract(T3) ;
         st_trans := transition accept
      |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End TimestampSpecSmall.