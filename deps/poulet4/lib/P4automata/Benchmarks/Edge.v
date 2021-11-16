Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.

Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.P4automata.Notations.

Require Import Poulet4.P4automata.BisimChecker.
Require Import Coq.Program.Equality.

Open Scope p4a.

Module Plain.
  Notation eth_size := 112.
  Notation mpls_size := 32.
  Notation eompls_size := 32.
  Notation ipv4_size := 156.
  Notation ipv6_size := 316.

  Inductive header: nat -> Type :=
  | HdrEth0: header eth_size
  | HdrEth1: header eth_size
  | HdrMPLS0: header mpls_size
  | HdrMPLS1: header mpls_size
  | HdrEoMPLS: header eompls_size
  | HdrIPVer: header 4
  | HdrIPv4: header ipv4_size
  | HdrIPv6: header ipv6_size.

  Derive Signature for header.
  Definition h32_eq_dec (x y: header 32) : {x = y} + {x <> y}.
  refine (
    match x with
    | HdrMPLS0 =>
      match y with
      | HdrMPLS0 => left eq_refl
      | HdrMPLS1 => right _
      | HdrEoMPLS => right _
      end
    | HdrMPLS1 =>
      match y with
      | HdrMPLS0 => right _
      | HdrMPLS1 => left eq_refl
      | HdrEoMPLS => right _
      end
    | HdrEoMPLS =>
      match y with
      | HdrMPLS0 => right _
      | HdrMPLS1 => right _
      | HdrEoMPLS => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Definition h4_eq_dec (x y: header 4) : {x = y} + {x <> y}.
  refine (
    match x with
    | HdrIPVer =>
      match y with
      | HdrIPVer => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Definition h112_eq_dec (x y: header 112) : {x = y} + {x <> y}.
  refine (
    match x with
    | HdrEth0 =>
      match y with
      | HdrEth0 => left eq_refl
      | HdrEth1 => right _
      end
    | HdrEth1 =>
      match y with
      | HdrEth0 => right _
      | HdrEth1 => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Definition h316_eq_dec (x y: header 316) : {x = y} + {x <> y}.
  refine (
    match x with
    | HdrIPv6 =>
      match y with
      | HdrIPv6 => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Definition h156_eq_dec (x y: header 156) : {x = y} + {x <> y}.
  refine (
    match x with
    | HdrIPv4 =>
      match y with
      | HdrIPv4 => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h32_eq_dec) ::
      (existT _ _ h4_eq_dec) ::
      (existT _ _ h112_eq_dec) ::
      (existT _ _ h316_eq_dec) ::
      (existT _ _ h156_eq_dec) ::
        nil).
  Defined.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.
  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
    solve_eqdec'.
  Defined.
  Global Instance header_finite: forall n, @Finite (header n) _ _.
    intros n; solve_indexed_finiteness n [32; 4 ; 112 ; 316 ; 156 ].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [
        existT _ _ HdrEth0
      ; existT _ _ HdrEth1
      ; existT _ _ HdrMPLS0
      ; existT _ _ HdrMPLS1
      ; existT _ _ HdrEoMPLS
      ; existT _ _ HdrIPVer
      ; existT _ _ HdrIPv4
      ; existT _ _ HdrIPv6
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

  Inductive state: Type :=
  | ParseEth0
  | ParseEth1
  | ParseMPLS0
  | ParseMPLS1
  | ParseEoMPLS
  | ParseIPVer
  | ParseIPv4
  | ParseIPv6.

  Definition states (s: state) : P4A.state state header :=
    match s with
    | ParseEth0 =>
      {| st_op := extract(HdrEth0);
        st_trans := transition select (| (EHdr HdrEth0)[111--96] |)
                                {{[| exact #b|1|0|0|0|1|0|0|0|0|1|0|0|0|1|1|1 |] ==> inl ParseMPLS0 ;;;
                                  [| exact #b|1|0|0|0|1|0|0|0|0|1|0|0|1|0|0|0 |] ==> inl ParseMPLS0 ;;;
                                  [| exact #b|0|0|0|0|1|0|0|0|0|0|0|0|0|0|0|0 |] ==> inl ParseIPv4 ;;;
                                  [| exact #b|1|0|0|0|0|1|1|0|1|1|0|1|1|1|0|1 |] ==> inl ParseIPv6 ;;;
                                  reject }}
      |}
    | ParseMPLS0 => 
      {| st_op := extract(HdrMPLS0);
        st_trans := transition select (| (EHdr HdrMPLS0)[24--24] |)
                                {{ [| hexact 0 |] ==> inl ParseMPLS1 ;;;
                                  [| hexact 1 |] ==> inl ParseIPVer ;;;
                                  reject
                                }}
      |}
    | ParseMPLS1 => 
      {| st_op := extract(HdrMPLS1);
        st_trans := transition (inl ParseIPVer)
      |}
    | ParseIPVer =>
      {| st_op := extract(HdrIPVer);
        st_trans := transition select (| EHdr HdrIPVer |)
                                {{ [| exact #b|0|0|0|0 |] ==> inl ParseEoMPLS;;;
                                  [| exact #b|0|1|0|0 |] ==> inl ParseIPv4;;;
                                  [| exact #b|0|1|1|0 |] ==> inl ParseIPv6;;;
                                  reject
                                }}
      |}
    | ParseEoMPLS =>
      {| st_op := extract(HdrEoMPLS);
        st_trans := transition (inl ParseEth1) |}
    | ParseIPv4 =>
      {| st_op := extract(HdrIPv4);
        st_trans := transition accept |}
    | ParseIPv6 =>
      {| st_op := extract(HdrIPv6);
        st_trans := transition accept |}
    | ParseEth1 =>
      {| st_op := extract(HdrEth1);
        st_trans := transition accept |}
    end.



  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [ParseEth0; ParseEth1; ParseMPLS0; ParseMPLS1; ParseEoMPLS; ParseIPVer; ParseIPv4; ParseIPv6] |}.
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

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).
End Plain.

Module Optimized.
Inductive state := | State_0_suff_1 | State_0_suff_3 | State_3 | State_0 | State_0_suff_2 | State_2 | State_3_suff_3 | State_3_suff_1 | State_1_suff_0 | State_3_suff_0 | State_1 | State_4 | State_3_suff_2 | State_2_suff_0.
Scheme Equality for state.
Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
Global Program Instance state_finite: @Finite state _ state_eq_dec :=
  {| enum := [State_0_suff_1; State_0_suff_3; State_3; State_0; State_0_suff_2; State_2; State_3_suff_3; State_3_suff_1; State_1_suff_0; State_3_suff_0; State_1; State_4; State_3_suff_2; State_2_suff_0] |}.
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
| buf_320: header 320
| buf_128: header 128
| buf_64: header 64
| buf_112: header 112
| buf_16: header 16
| buf_304: header 304
| buf_240: header 240
| buf_144: header 144
| buf_176: header 176
| buf_208: header 208.
Definition h320_eq_dec (x y: header 320) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_320 =>
    match y with
    | buf_320 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h64_eq_dec (x y: header 64) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_64 =>
    match y with
    | buf_64 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h128_eq_dec (x y: header 128) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_128 =>
    match y with
    | buf_128 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h16_eq_dec (x y: header 16) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_16 =>
    match y with
    | buf_16 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h112_eq_dec (x y: header 112) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_112 =>
    match y with
    | buf_112 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h304_eq_dec (x y: header 304) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_304 =>
    match y with
    | buf_304 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h240_eq_dec (x y: header 240) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_240 =>
    match y with
    | buf_240 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h144_eq_dec (x y: header 144) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_144 =>
    match y with
    | buf_144 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h176_eq_dec (x y: header 176) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_176 =>
    match y with
    | buf_176 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h208_eq_dec (x y: header 208) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_208 =>
    match y with
    | buf_208 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Derive Signature for header.
Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
  solve_header_eqdec_ n x y
    ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h320_eq_dec) ::
     (existT _ _ h64_eq_dec) ::
     (existT _ _ h128_eq_dec) ::
     (existT _ _ h16_eq_dec) ::
     (existT _ _ h112_eq_dec) ::
     (existT _ _ h304_eq_dec) ::
     (existT _ _ h240_eq_dec) ::
     (existT _ _ h144_eq_dec) ::
     (existT _ _ h176_eq_dec) ::
     (existT _ _ h208_eq_dec) ::
      nil).
Defined.

Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.
Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  solve_eqdec'.
Defined.
Global Instance header_finite: forall n, @Finite (header n) _ _.
  intros n; solve_indexed_finiteness n [320; 64 ; 128 ; 16 ; 112 ; 304 ; 240 ; 144 ; 176 ; 208 ].
Qed.

Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
  {| enum := [
      existT _ _ buf_320
    ; existT _ _ buf_128
    ; existT _ _ buf_64
    ; existT _ _ buf_112
    ; existT _ _ buf_16
    ; existT _ _ buf_304
    ; existT _ _ buf_240
    ; existT _ _ buf_144
    ; existT _ _ buf_176
    ; existT _ _ buf_208
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
  | State_0 => {|
    st_op := extract(buf_112);
    st_trans := transition select (| (EHdr buf_112)[15 -- 15], (EHdr buf_112)[14 -- 14], (EHdr buf_112)[13 -- 13], (EHdr buf_112)[12 -- 12], (EHdr buf_112)[11 -- 11], (EHdr buf_112)[10 -- 10], (EHdr buf_112)[9 -- 9], (EHdr buf_112)[8 -- 8], (EHdr buf_112)[7 -- 7], (EHdr buf_112)[6 -- 6], (EHdr buf_112)[5 -- 5], (EHdr buf_112)[4 -- 4], (EHdr buf_112)[3 -- 3], (EHdr buf_112)[2 -- 2], (EHdr buf_112)[1 -- 1], (EHdr buf_112)[0 -- 0], (EHdr buf_112)[111 -- 111], (EHdr buf_112)[110 -- 110], (EHdr buf_112)[109 -- 109], (EHdr buf_112)[108 -- 108], (EHdr buf_112)[107 -- 107], (EHdr buf_112)[106 -- 106], (EHdr buf_112)[105 -- 105], (EHdr buf_112)[104 -- 104], (EHdr buf_112)[103 -- 103], (EHdr buf_112)[102 -- 102], (EHdr buf_112)[101 -- 101], (EHdr buf_112)[100 -- 100], (EHdr buf_112)[99 -- 99], (EHdr buf_112)[98 -- 98], (EHdr buf_112)[97 -- 97], (EHdr buf_112)[96 -- 96], (EHdr buf_112)[15 -- 15], (EHdr buf_112)[14 -- 14], (EHdr buf_112)[13 -- 13], (EHdr buf_112)[12 -- 12], (EHdr buf_112)[11 -- 11], (EHdr buf_112)[10 -- 10], (EHdr buf_112)[9 -- 9], (EHdr buf_112)[8 -- 8], (EHdr buf_112)[7 -- 7], (EHdr buf_112)[6 -- 6], (EHdr buf_112)[5 -- 5], (EHdr buf_112)[4 -- 4], (EHdr buf_112)[3 -- 3], (EHdr buf_112)[2 -- 2], (EHdr buf_112)[1 -- 1], (EHdr buf_112)[0 -- 0], (EHdr buf_112)[15 -- 15], (EHdr buf_112)[14 -- 14], (EHdr buf_112)[13 -- 13], (EHdr buf_112)[12 -- 12], (EHdr buf_112)[11 -- 11], (EHdr buf_112)[10 -- 10], (EHdr buf_112)[9 -- 9], (EHdr buf_112)[8 -- 8], (EHdr buf_112)[7 -- 7], (EHdr buf_112)[6 -- 6], (EHdr buf_112)[5 -- 5], (EHdr buf_112)[4 -- 4], (EHdr buf_112)[3 -- 3], (EHdr buf_112)[2 -- 2], (EHdr buf_112)[1 -- 1], (EHdr buf_112)[0 -- 0]|) {{
      (* [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> accept ;;; *)
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|0, exact #b|1, exact #b|1, exact #b|0, exact #b|1, exact #b|1, exact #b|1, exact #b|0, exact #b|1, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_0_suff_1 ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|1, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_0_suff_2 ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_0_suff_3 ;;;
      (* [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> accept ;;; *)
      reject
    }}
  |}
  | State_0_suff_1 => {|
    st_op := extract(buf_320);
    st_trans := transition accept;
  |}
  | State_0_suff_2 => {|
    st_op := extract(buf_16);
    st_trans := transition inl State_2;
  |}
  | State_0_suff_3 => {|
    st_op := extract(buf_16);
    st_trans := transition inl State_3;
  |}
  | State_1 => {|
    st_op := extract(buf_16);
    st_trans := transition select (| (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0], (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0], (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0], (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0]|) {{
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_1_suff_0 ;;;
      reject
    }}
  |}
  | State_1_suff_0 => {|
    st_op := extract(buf_128);
    st_trans := transition accept;
  |}
  | State_2 => {|
    st_op := extract(buf_16);
    st_trans := transition select (| (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0], (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0], (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0], (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0]|) {{
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_2_suff_0 ;;;
      reject
    }}
  |}
  | State_2_suff_0 => {|
    st_op := extract(buf_304);
    st_trans := transition accept;
  |}
  | State_3 => {|
    st_op := extract(buf_16);
    st_trans := transition select (| (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0], (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0], (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0], (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0]|) {{
      [| *, *, *, *, exact #b|0, exact #b|1, exact #b|0, exact #b|1, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_3_suff_0 ;;;
      [| *, *, *, *, exact #b|0, exact #b|1, exact #b|1, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_3_suff_1 ;;;
      [| *, *, *, *, exact #b|0, exact #b|1, exact #b|1, exact #b|1, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_3_suff_2 ;;;
      [| *, *, *, *, exact #b|1, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_3_suff_3 ;;;
      reject
    }}
  |}
  | State_3_suff_0 => {|
    st_op := extract(buf_144);
    st_trans := transition accept;
  |}
  | State_3_suff_1 => {|
    st_op := extract(buf_176);
    st_trans := transition accept;
  |}
  | State_3_suff_2 => {|
    st_op := extract(buf_208);
    st_trans := transition accept;
  |}
  | State_3_suff_3 => {|
    st_op := extract(buf_240);
    st_trans := transition accept;
  |}
  | State_4 => {|
    st_op := extract(buf_64);
    st_trans := transition select (| (EHdr buf_64)[15 -- 15], (EHdr buf_64)[14 -- 14], (EHdr buf_64)[13 -- 13], (EHdr buf_64)[12 -- 12], (EHdr buf_64)[11 -- 11], (EHdr buf_64)[10 -- 10], (EHdr buf_64)[9 -- 9], (EHdr buf_64)[8 -- 8], (EHdr buf_64)[7 -- 7], (EHdr buf_64)[6 -- 6], (EHdr buf_64)[5 -- 5], (EHdr buf_64)[4 -- 4], (EHdr buf_64)[3 -- 3], (EHdr buf_64)[2 -- 2], (EHdr buf_64)[1 -- 1], (EHdr buf_64)[0 -- 0], (EHdr buf_64)[31 -- 31], (EHdr buf_64)[30 -- 30], (EHdr buf_64)[29 -- 29], (EHdr buf_64)[28 -- 28], (EHdr buf_64)[27 -- 27], (EHdr buf_64)[26 -- 26], (EHdr buf_64)[25 -- 25], (EHdr buf_64)[24 -- 24], (EHdr buf_64)[23 -- 23], (EHdr buf_64)[22 -- 22], (EHdr buf_64)[21 -- 21], (EHdr buf_64)[20 -- 20], (EHdr buf_64)[19 -- 19], (EHdr buf_64)[18 -- 18], (EHdr buf_64)[17 -- 17], (EHdr buf_64)[16 -- 16], (EHdr buf_64)[47 -- 47], (EHdr buf_64)[46 -- 46], (EHdr buf_64)[45 -- 45], (EHdr buf_64)[44 -- 44], (EHdr buf_64)[43 -- 43], (EHdr buf_64)[42 -- 42], (EHdr buf_64)[41 -- 41], (EHdr buf_64)[40 -- 40], (EHdr buf_64)[39 -- 39], (EHdr buf_64)[38 -- 38], (EHdr buf_64)[37 -- 37], (EHdr buf_64)[36 -- 36], (EHdr buf_64)[35 -- 35], (EHdr buf_64)[34 -- 34], (EHdr buf_64)[33 -- 33], (EHdr buf_64)[32 -- 32], (EHdr buf_64)[63 -- 63], (EHdr buf_64)[62 -- 62], (EHdr buf_64)[61 -- 61], (EHdr buf_64)[60 -- 60], (EHdr buf_64)[59 -- 59], (EHdr buf_64)[58 -- 58], (EHdr buf_64)[57 -- 57], (EHdr buf_64)[56 -- 56], (EHdr buf_64)[55 -- 55], (EHdr buf_64)[54 -- 54], (EHdr buf_64)[53 -- 53], (EHdr buf_64)[52 -- 52], (EHdr buf_64)[51 -- 51], (EHdr buf_64)[50 -- 50], (EHdr buf_64)[49 -- 49], (EHdr buf_64)[48 -- 48]|) {{
      [| *, *, *, *, *, *, *, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|1, *, *, *, *, *, *, *, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject ;;;
      [| *, *, *, *, *, *, *, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|1, *, *, *, *, *, *, *, *, exact #b|0, exact #b|1, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject ;;;
      [| *, *, *, *, *, *, *, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|1, *, *, *, *, *, *, *, *, exact #b|0, exact #b|1, exact #b|1, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject ;;;
      [| *, *, *, *, *, *, *, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject ;;;
      [| *, *, *, *, *, *, *, exact #b|1, *, *, *, *, *, *, *, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject ;;;
      [| *, *, *, *, *, *, *, exact #b|1, *, *, *, *, *, *, *, *, exact #b|0, exact #b|1, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject ;;;
      [| *, *, *, *, *, *, *, exact #b|1, *, *, *, *, *, *, *, *, exact #b|0, exact #b|1, exact #b|1, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject ;;;
      reject
    }}
  |}
end.
Program Definition aut: Syntax.t state header :=
  {| t_states := states |}.
Solve Obligations with (destruct s; cbv; Lia.lia).
End Optimized.