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

Module ParseOne.
  Inductive state :=
  | Start.

  Equations state_eq_dec (l: state) (r: state) : {l = r} + {l <> r} :=
  { state_eq_dec Start Start := left eq_refl }.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Bit.

  Definition sz (h: header) :=
    match h with
    | Bit => 1
    end.

  Equations header_eq_dec (x: header) (y: header) : {x = y} + {x <> y} :=
  { header_eq_dec Bit Bit := left eq_refl }.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) : WP.P4A.state state sz :=
    match s with
    | Start =>
      {| st_op := extract(Bit);
         st_trans := transition select (| EHdr Bit |) {{
           [| exact #b|1 |] ==> accept ;;;
            @reject state
         }}
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).

End ParseOne.

Module ParseZero.
  Inductive state :=
  | Start.

  Equations state_eq_dec (l: state) (r: state) : {l = r} + {l <> r} :=
  { state_eq_dec Start Start := left eq_refl }.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Bit : header.

  Definition sz (h: header): nat :=
    match h with
    | Bit => 1
    end.

  Equations header_eq_dec (x: header) (y: header) : {x = y} + {x <> y} :=
  { header_eq_dec Bit Bit := left eq_refl }.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) : WP.P4A.state state sz :=
    match s with
    | Start =>
      {| st_op := extract(Bit);
         st_trans := transition select (| EHdr Bit |) {{
           [| exact #b|0 |] ==> accept ;;;
            @reject state
         }}
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).

End ParseZero.

Module OneZero.
  Definition aut := Sum.sum ParseOne.aut ParseZero.aut.
End OneZero.

Module TwoOnesChunk.
  Inductive state :=
  | Start.

  Equations state_eq_dec (l: state) (r: state) : {l = r} + {l <> r} :=
  { state_eq_dec Start Start := left eq_refl }.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Bits : header.

  Equations header_eq_dec (x: header) (y: header) : {x = y} + {x <> y} :=
  { header_eq_dec Bits Bits := left eq_refl }.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition sz (h: header) : nat :=
    match h with
    | Bits => 2
    end.

  Definition states (s: state) : WP.P4A.state state sz :=
    match s with
    | Start =>
      {| st_op := extract(Bits);
         st_trans := transition select (| EHdr Bits |) {{
           [| exact #b|1|1 |] ==> accept ;;;
            @reject state
         }}
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).
End TwoOnesChunk.

Module TwoOnesBucket.
  Inductive state :=
  | Start
  | Next.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Bits
  | Val.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition sz (h: header): nat :=
    match h with
    | Bits => 2
    | Val => 1
    end.

  Definition states (s: state) : WP.P4A.state state sz :=
    match s with
    | Start =>
      {| st_op :=
          extract(Val) ;;
          Bits <- EConcat (m := 1) (EHdr Val) ((EHdr (sz := sz) Bits)[1--1]) ;
         st_trans := transition select (| EHdr Val |) {{
           [| exact #b|1 |] ==> inl Next ;;;
            @reject state
         }}
      |}
    | Next =>
      {| st_op :=
          extract(Val) ;;
          Bits <- EConcat (m := 1) (ESlice _ (EHdr (sz := sz) Bits) 0 0) (EHdr Val) ;
         st_trans := transition select (| EHdr Val |) {{
           [| exact #b|1 |] ==> accept ;;;
            @reject state
         }}
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).

End TwoOnesBucket.
