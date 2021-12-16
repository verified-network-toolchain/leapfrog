Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.

Require Import Leapfrog.Syntax.
Require Import Leapfrog.FinType.
Require Import Leapfrog.Sum.
Require Import Leapfrog.Syntax.
Require Import Leapfrog.Notations.
Require Import Leapfrog.BisimChecker.

Open Scope p4a.

Module Reference.
  Inductive state: Set :=
  | SPref
  | SDest
  | SSrc
  | SProto.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | HPref
  | HDest
  | HSrc
  | HProto.

  Definition sz (h: header): nat :=
    match h with
    | HPref => 64
    | HDest => 48
    | HSrc => 48
    | HProto => 16
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) : Syntax.state state sz :=
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

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).

End Reference.

Module Combined.
  Inductive state :=
  | Parse.

  Equations state_eq_dec (h1 h2: state) : {h1 = h2} + {h1 <> h2} :=
  { state_eq_dec Parse Parse := left eq_refl }.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | HdrVar.

  Equations header_eq_dec (h1 h2: header) : {h1 = h2} + {h1 <> h2} :=
  { header_eq_dec HdrVar HdrVar := left eq_refl }.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition sz (h: header): nat :=
    match h with
    | HdrVar => 176
    end.

  Definition states (s: state) : Syntax.state state sz :=
    match s with
    | Parse =>
      {| st_op := extract(HdrVar);
        st_trans := transition select (| (EHdr (Hdr_sz := sz) HdrVar)[176 -- 160] |) {{
          [| exact #b|1|0|0|0|0|0|0|0|0|0|0|0|0|0|0|0 |] ==> accept ;;;
            @reject state
        }}
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).

End Combined.

Module RefComb.
  Definition aut := sum Reference.aut Combined.aut.
End RefComb.
