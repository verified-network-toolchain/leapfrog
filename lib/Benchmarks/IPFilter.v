Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Leapfrog.Syntax.
Require Import Leapfrog.FinType.
Require Import Leapfrog.Sum.
Require Import Leapfrog.Syntax.

Require Import Leapfrog.BisimChecker.

Require Import Leapfrog.Notations.

Open Scope p4a.

Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.

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
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | HdrIP
  | HdrUDP
  | HdrTCP.

  Definition sz (h: header) : N :=
    match h with
    | HdrIP => 64
    | HdrUDP => 32
    | HdrTCP => 64
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) :=
    match s with
    | ParseIP =>
      {| st_op := extract(HdrIP);
         st_trans := transition select (| (EHdr (Hdr_sz := sz) HdrIP)[43 -- 40] |) {{
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

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (try (destruct s; vm_compute; exact eq_refl) || (destruct h; simpl sz; Lia.lia)).


End UDPInterleaved.

Module UDPCombined.
  Inductive state :=
  | ParsePref
  | ParseSuf.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | HdrIP
  | HdrPref.

  Definition sz (h: header) : N :=
    match h with
    | HdrIP => 64
    | HdrPre => 32
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) :=
    match s with
    | ParsePref =>
      {| st_op :=
          extract(HdrIP) ;;
          extract(HdrPref) ;
          st_trans := transition select (| (EHdr (Hdr_sz := sz) HdrIP)[43 -- 40] |) {{
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

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (try (destruct s; vm_compute; exact eq_refl) || (destruct h; simpl sz; Lia.lia)).


End UDPCombined.

Module IPFilter.
  Definition aut := Sum.sum UDPCombined.aut UDPInterleaved.aut.
End IPFilter.
