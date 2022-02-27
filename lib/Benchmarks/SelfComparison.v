Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.

Require Import Leapfrog.Syntax.
Require Import Leapfrog.FinType.
Require Import Leapfrog.Sum.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.Notations.
Require Import Leapfrog.BisimChecker.

Open Scope p4a.

Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.

Notation eth_size := 112.
Notation ip_size := 160.
Notation vlan_size := 32.
Notation udp_size := 64.

(*
This example is an undefined-value example inspired by the running
example in the SafeP4 paper (https://arxiv.org/pdf/1906.07223.pdf).
*)

Module ReadUndef.
  Inductive state :=
  | ParseEth
  | DefaultVLAN
  | ParseVLAN
  | ParseIP
  | ParseUDP.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | HdrEth
  | HdrIP
  | HdrVLAN
  | HdrUDP.

  Definition sz (h: header) : N :=
    match h with
    | HdrEth => 112
    | HdrIP => 160
    | HdrVLAN => 32
    | HdrUDP => 64
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) : P4A.state state sz :=
    match s with
    | ParseEth =>
      {| st_op := extract(HdrEth);
         st_trans := transition select (| (EHdr (Hdr_sz := sz) HdrEth)[0 -- 0] |) {{
                                    [| exact #b|0 |] ==> inl DefaultVLAN ;;;
                                    [| exact #b|1 |] ==> inl ParseVLAN ;;;
                                    reject
                                }}
      |}
    | DefaultVLAN =>
      {| st_op := HdrVLAN <- ELit _ (Ntuple.n_tuple_repeat 32 false) ;;
                  extract(HdrIP);
         st_trans := transition (inl ParseUDP)
      |}
    | ParseIP =>
      {| st_op := extract(HdrIP);
         st_trans := transition (inl ParseUDP)
      |}
    | ParseVLAN =>
      {| st_op := extract(HdrVLAN);
         st_trans := transition (inl ParseIP)
      |}
    | ParseUDP =>
      {| st_op := extract(HdrUDP);
         st_trans := transition select (| (EHdr (Hdr_sz := sz) HdrVLAN)[3--0] |) {{
                                    [| exact #b|1|1|1|1 |] ==> reject ;;;
                                    accept
                                }}
      |}
    end.

  Program Definition aut: Syntax.t state _ :=
    {| t_states := states |}.
  Solve Obligations with (try (destruct s; vm_compute; exact eq_refl) || (destruct h; simpl sz; Lia.lia)).


End ReadUndef.


Module ReadUndefIncorrect.
  Inductive state :=
  | ParseEth
  | DefaultVLAN
  | ParseVLAN
  | ParseIP
  | ParseUDP.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | HdrEth
  | HdrIP
  | HdrVLAN
  | HdrUDP.

  Definition sz (h: header) : N :=
    match h with
    | HdrEth => 112
    | HdrIP => 160
    | HdrVLAN => 32
    | HdrUDP => 64
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) : P4A.state state sz :=
    match s with
    | ParseEth =>
      {| st_op := extract(HdrEth);
         st_trans := transition select (| (EHdr (Hdr_sz := sz) HdrEth)[0 -- 0] |) {{
                                    [| exact #b|0 |] ==> inl DefaultVLAN ;;;
                                    [| exact #b|1 |] ==> inl ParseVLAN ;;;
                                    reject
                                }}
      |}
    | DefaultVLAN =>
      {| st_op := extract(HdrIP);
         st_trans := transition (inl ParseUDP)
      |}
    | ParseIP =>
      {| st_op := extract(HdrIP);
         st_trans := transition (inl ParseUDP)
      |}
    | ParseVLAN =>
      {| st_op := extract(HdrVLAN);
         st_trans := transition (inl ParseIP)
      |}
    | ParseUDP =>
      {| st_op := extract(HdrUDP);
         st_trans := transition select (| (EHdr (Hdr_sz := sz) HdrVLAN)[3--0] |) {{
                                    [| exact #b|1|1|1|1 |] ==> reject ;;;
                                    accept
                                }}
      |}
    end.

  Program Definition aut: Syntax.t state _ :=
    {| t_states := states |}.
  Solve Obligations with (try (destruct s; vm_compute; exact eq_refl) || (destruct h; simpl sz; Lia.lia)).


End ReadUndefIncorrect.
