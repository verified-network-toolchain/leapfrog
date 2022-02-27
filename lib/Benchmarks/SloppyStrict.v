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

Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.

Ltac prep_equiv :=
  unfold Equivalence.equiv, RelationClasses.complement in *;
  program_simpl; try congruence.

Obligation Tactic := prep_equiv.


Module Sloppy.
  Inductive state :=
  | ParseEthernet
  | ParseIPv4
  | ParseIPv6
  .

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | HdrEthernet
  | HdrIPv4
  | HdrIPv6.

  Definition sz (h: header): N :=
    match h with
    | HdrEthernet => 112
    | HdrIPv4 => 128
    | HdrIPv6 => 288
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) : WP.P4A.state state sz :=
    match s with
    | ParseEthernet =>
      {| st_op := extract(HdrEthernet) ;
         st_trans := transition select (| ESlice _ (EHdr (Hdr_sz := sz) HdrEthernet) 111 96 |) {{
           [| hexact_w(16) 0x86dd |] ==> inl ParseIPv6 ;;;
            inl ParseIPv4
         }}
      |}
    | ParseIPv4 =>
      {| st_op := extract(HdrIPv4) ;
         st_trans := transition accept
      |}
    | ParseIPv6 =>
      {| st_op := extract(HdrIPv6) ;
         st_trans := transition accept
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (try (destruct s; vm_compute; exact eq_refl) || (destruct h; simpl sz; Lia.lia)).

End Sloppy.

Module Strict.

  Inductive state :=
  | ParseEthernet
  | ParseIPv4
  | ParseIPv6
  .

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | HdrEthernet
  | HdrIPv4
  | HdrIPv6.

  Definition sz (h: header): N :=
    match h with
    | HdrEthernet => 112
    | HdrIPv4 => 128
    | HdrIPv6 => 288
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Notation Ehdr := (EHdr (Hdr_sz := sz)).

  Definition states (s: state) : WP.P4A.state state sz :=
    match s with
    | ParseEthernet =>
      {| st_op := extract(HdrEthernet) ;
         st_trans := transition select (| ESlice _ (Ehdr HdrEthernet) 111 96 |) {{
           [| hexact_w(16) 0x86dd |] ==> inl ParseIPv6 ;;;
           [| hexact_w(16) 0x8600 |] ==> inl ParseIPv4 ;;;
            reject
         }}
      |}
    | ParseIPv4 =>
      {| st_op := extract(HdrIPv4) ;
         st_trans := transition accept
      |}
    | ParseIPv6 =>
      {| st_op := extract(HdrIPv6) ;
         st_trans := transition accept
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (try (destruct s; vm_compute; exact eq_refl) || (destruct h; simpl sz; Lia.lia)).

End Strict.

Module SloppyStrict.
  Definition aut := Sum.sum Sloppy.aut Strict.aut.
End SloppyStrict.
