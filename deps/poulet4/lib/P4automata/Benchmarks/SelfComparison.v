Require Coq.Classes.EquivDec.
Require Import Coq.Arith.PeanoNat.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.P4automata.Notations.

Require Import Poulet4.P4automata.BisimChecker.

Open Scope p4a.

(* These sizes should be bigger. *)
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
  Qed.

  Inductive header : nat -> Type :=
  | HdrEth: header eth_size
  | HdrIP: header ip_size
  | HdrVLAN: header vlan_size
  | HdrUDP: header udp_size.

  Derive Signature for header.

  Definition h112_eq_dec (x y: header 112) : {x = y} + {x <> y}.
    refine (
        match x, y with 
        | HdrEth, HdrEth => left eq_refl
        | _, _ => idProp
        end);
      intros H; inversion H.
  Defined.

  Definition h160_eq_dec (x y: header 160) : {x = y} + {x <> y}.
    refine (
        match x, y with 
        | HdrIP, HdrIP => left eq_refl
        | _, _ => idProp
        end);
      intros H; inversion H.
  Defined.

  Definition h32_eq_dec (x y: header 32) : {x = y} + {x <> y}.
    refine (
        match x, y with 
        | HdrVLAN, HdrVLAN => left eq_refl
        | _, _ => idProp
        end);
      intros H; inversion H.
  Defined.

  Definition h64_eq_dec (x y: header 64) : {x = y} + {x <> y}.
    refine (
        match x, y with 
        | HdrUDP, HdrUDP => left eq_refl
        | _, _ => idProp
        end);
      intros H; inversion H.
  Defined.

  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y 
      [existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h112_eq_dec;
       existT _ _ h160_eq_dec;
       existT _ _ h32_eq_dec;
       existT _ _ h64_eq_dec].
  Defined. 

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (H' header) eq.
  Proof.
    solve_eqdec'.
  Qed.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [eth_size;ip_size;vlan_size;udp_size].
  Qed.
  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ HdrEth ;
                 existT _ _ HdrIP ;
                 existT _ _ HdrVLAN ;
                 existT _ _ HdrUDP ] |}.
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

  Definition states (s: state) : P4A.state state header :=
    match s with
    | ParseEth =>
      {| st_op := extract(HdrEth);
         st_trans := transition select (| (EHdr HdrEth)[0 -- 0] |) {{
                                    [| exact #b|0 |] ==> inl DefaultVLAN ;;;
                                    [| exact #b|1 |] ==> inl ParseVLAN ;;;
                                    reject
                                }}
      |}
    | DefaultVLAN =>
      {| st_op := HdrVLAN <- ELit (Ntuple.n_tuple_repeat _ false) ;;
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
         st_trans := transition select (| (EHdr HdrVLAN)[3--0] |) {{
                                    [| exact #b|1|1|1|1 |] ==> reject ;;;
                                    accept
                                }}
      |}
    end.

  Program Definition aut: Syntax.t state _ :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

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
  Qed.

  Inductive header : nat -> Type :=
  | HdrEth: header eth_size
  | HdrIP: header ip_size
  | HdrVLAN: header vlan_size
  | HdrUDP: header udp_size.

  Derive Signature for header.

  Definition h112_eq_dec (x y: header 112) : {x = y} + {x <> y}.
    refine (
        match x, y with 
        | HdrEth, HdrEth => left eq_refl
        | _, _ => idProp
        end);
      intros H; inversion H.
  Defined.

  Definition h160_eq_dec (x y: header 160) : {x = y} + {x <> y}.
    refine (
        match x, y with 
        | HdrIP, HdrIP => left eq_refl
        | _, _ => idProp
        end);
      intros H; inversion H.
  Defined.

  Definition h32_eq_dec (x y: header 32) : {x = y} + {x <> y}.
    refine (
        match x, y with 
        | HdrVLAN, HdrVLAN => left eq_refl
        | _, _ => idProp
        end);
      intros H; inversion H.
  Defined.

  Definition h64_eq_dec (x y: header 64) : {x = y} + {x <> y}.
    refine (
        match x, y with 
        | HdrUDP, HdrUDP => left eq_refl
        | _, _ => idProp
        end);
      intros H; inversion H.
  Defined.

  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y 
      [existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h112_eq_dec;
       existT _ _ h160_eq_dec;
       existT _ _ h32_eq_dec;
       existT _ _ h64_eq_dec].
  Defined. 

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (H' header) eq.
  Proof.
    solve_eqdec'.
  Qed.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [eth_size;ip_size;vlan_size;udp_size].
  Qed.
  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ HdrEth ;
                 existT _ _ HdrIP ;
                 existT _ _ HdrVLAN ;
                 existT _ _ HdrUDP ] |}.
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

  Definition states (s: state) : P4A.state state header :=
    match s with
    | ParseEth =>
      {| st_op := extract(HdrEth);
         st_trans := transition select (| (EHdr HdrEth)[0 -- 0] |) {{
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
         st_trans := transition select (| (EHdr HdrVLAN)[3--0] |) {{
                                    [| exact #b|1|1|1|1 |] ==> reject ;;;
                                    accept
                                }}
      |}
    end.

  Program Definition aut: Syntax.t state _ :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End ReadUndefIncorrect.
