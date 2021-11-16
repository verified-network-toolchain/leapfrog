Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.P4automata.BisimChecker.

Require Import Poulet4.P4automata.Notations.

Open Scope p4a.


Ltac prep_equiv :=
  unfold Equivalence.equiv, RelationClasses.complement in *;
  program_simpl; try congruence.

Obligation Tactic := prep_equiv.

Module VerySimple.

(* 
ethernet {
	fields {
		dstAddr : 48 : extract,
		srcAddr : 48 : extract,
		etherType : 16 : extract,
	}
	next_header = map(etherType) {
		0x8100 : ieee802-1q,
		0x0800 : ipv4,
	}
}

ieee802-1q {
	fields {
		pcp : 3 : extract,
		cfi : 1,
		vid : 12 : extract,
		etherType : 16 : extract,
	}
	next_header = map(etherType) {
		0x8100 : ieee802-1q,
		0x0800 : ipv4,
	}
	max_var = vlan
	max = 2
}

ipv4 {
	fields {
		dummy : 160,
	}
} *)


  Inductive state := | Ethernet | VLan1 | VLan2 | IPV4 | Trailer.
  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [Ethernet; VLan1; VLan2; IPV4; Trailer] |}.
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
  | H_Eth: header 112
  | H_VLan: header 32
  | H_IP: header 160.
  Definition h112_eq_dec (x y: header 112) : {x = y} + {x <> y}.
  refine (
    match x with
    | H_Eth =>
      match y with
      | H_Eth => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Definition h32_eq_dec (x y: header 32) : {x = y} + {x <> y}.
  refine (
    match x with
    | H_VLan =>
      match y with
      | H_VLan => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Definition h160_eq_dec (x y: header 160) : {x = y} + {x <> y}.
  refine (
    match x with
    | H_IP =>
      match y with
      | H_IP => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Derive Signature for header.
  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h112_eq_dec) ::
      (existT _ _ h32_eq_dec) ::
      (existT _ _ h160_eq_dec) ::
        nil).
  Defined.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.
  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
    solve_eqdec'.
  Defined.
  Global Instance header_finite: forall n, @Finite (header n) _ _.
    intros n; solve_indexed_finiteness n [112; 32 ; 160 ].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [
        existT _ _ H_Eth
      ; existT _ _ H_VLan
      ; existT _ _ H_IP
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
    | Ethernet => {|
      st_op := extract(H_Eth);
      st_trans := transition select (| (EHdr H_Eth)[111 -- 96] |) {{
        [| hexact 0x0800 |] ==> inl IPV4 ;;;
        [| hexact 0x8100 |] ==> inl VLan1 ;;;
        reject
      }}
    |}
    | VLan1 => {|
      st_op := extract(H_VLan);
      st_trans := transition select (| (EHdr H_VLan)[31 -- 16]|) {{
        [| hexact 0x0800 |] ==> inl IPV4 ;;;
        [| hexact 0x8100 |] ==> inl VLan2 ;;;
        inl Trailer
      }}
    |}
    | VLan2 => {|
      st_op := extract(H_VLan);
      st_trans := transition select (| (EHdr H_VLan)[31 -- 16]|) {{
        [| hexact 0x0800 |] ==> inl IPV4 ;;;
        reject
      }}
    |}
    | IPV4 => {|
      st_op := extract(H_IP);
      st_trans := transition accept
    |}
    | Trailer => {|
      st_op := extract(H_VLan);
      st_trans := transition reject
    |}
    end.

    Program Definition aut: Syntax.t state header :=
      {| t_states := states |}.
    Solve Obligations with (destruct s; cbv; Lia.lia).
    
End VerySimple.


Module Simple.

(* 
ethernet {
	fields {
		dstAddr : 48 : extract,
		srcAddr : 48 : extract,
		etherType : 16 : extract,
	}
	next_header = map(etherType) {
		0x8100 : ieee802-1q,
		0x0800 : ipv4,
	}
}

ieee802-1q {
	fields {
		pcp : 3 : extract,
		cfi : 1,
		vid : 12 : extract,
		etherType : 16 : extract,
	}
	next_header = map(etherType) {
		0x8100 : ieee802-1q,
		0x0800 : ipv4,
	}
	max_var = vlan
	max = 2
}

ipv4 {
	fields {
		dummy : 160,
	}
} *)


  Inductive state := | Ethernet | VLan1 | VLan2 | IPV4 | Trailer.
  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [Ethernet; VLan1; VLan2; IPV4; Trailer] |}.
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
  | H_Eth: header 112
  | H_VLan: header 32
  | H_IP: header 160.
  Definition h112_eq_dec (x y: header 112) : {x = y} + {x <> y}.
  refine (
    match x with
    | H_Eth =>
      match y with
      | H_Eth => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Definition h32_eq_dec (x y: header 32) : {x = y} + {x <> y}.
  refine (
    match x with
    | H_VLan =>
      match y with
      | H_VLan => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Definition h160_eq_dec (x y: header 160) : {x = y} + {x <> y}.
  refine (
    match x with
    | H_IP =>
      match y with
      | H_IP => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Derive Signature for header.
  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h112_eq_dec) ::
      (existT _ _ h32_eq_dec) ::
      (existT _ _ h160_eq_dec) ::
        nil).
  Defined.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.
  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
    solve_eqdec'.
  Defined.
  Global Instance header_finite: forall n, @Finite (header n) _ _.
    intros n; solve_indexed_finiteness n [112; 32 ; 160 ].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [
        existT _ _ H_Eth
      ; existT _ _ H_VLan
      ; existT _ _ H_IP
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
    | Ethernet => {|
      st_op := extract(H_Eth);
      st_trans := transition select (| (EHdr H_Eth)[99 -- 96], (EHdr H_Eth)[103 -- 100], (EHdr H_Eth)[107 -- 104], (EHdr H_Eth)[111 -- 108] |) {{
        [| hexact 0x0, hexact 0x8, hexact 0x0, hexact 0x0 |] ==> inl IPV4 ;;;
        [| hexact 0x8, hexact 0x1, hexact 0x0, hexact 0x0 |] ==> inl VLan1 ;;;
        reject
      }}
    |}
    | VLan1 => {|
      st_op := extract(H_VLan);
      st_trans := transition select (| (EHdr H_VLan)[19 -- 16], (EHdr H_VLan)[23 -- 20], (EHdr H_VLan)[27 -- 24], (EHdr H_VLan)[31 -- 28]|) {{
        [| hexact 0x0, hexact 0x8, hexact 0x0, hexact 0x0 |] ==> inl IPV4 ;;;
        [| hexact 0x8, hexact 0x1, hexact 0x0, hexact 0x0 |] ==> inl VLan2 ;;;
        inl Trailer
      }}
    |}
    | VLan2 => {|
      st_op := extract(H_VLan);
      st_trans := transition select (| (EHdr H_VLan)[19 -- 16], (EHdr H_VLan)[23 -- 20], (EHdr H_VLan)[27 -- 24], (EHdr H_VLan)[31 -- 28]|) {{
        [| hexact 0x0, hexact 0x8, hexact 0x0, hexact 0x0 |] ==> inl IPV4 ;;;
        reject
      }}
    |}
    | IPV4 => {|
      st_op := extract(H_IP);
      st_trans := transition accept
    |}
    | Trailer => {|
      st_op := extract(H_VLan);
      st_trans := transition reject
    |}
    end.

    Program Definition aut: Syntax.t state header :=
      {| t_states := states |}.
    Solve Obligations with (destruct s; cbv; Lia.lia).
    
End Simple.


Module Optimized.
Inductive state := | State_1_suff_1 | State_0_suff_0 | State_1 | State_0 | State_1_suff_0 | State_0_suff_1.
Scheme Equality for state.
Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
Global Program Instance state_finite: @Finite state _ state_eq_dec :=
  {| enum := [State_1_suff_1; State_0_suff_0; State_1; State_0; State_1_suff_0; State_0_suff_1] |}.
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
| buf_112: header 112
| buf_16: header 16
| buf_160: header 160
| buf_64: header 64
| buf_96: header 96.
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
Definition h96_eq_dec (x y: header 96) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_96 =>
    match y with
    | buf_96 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h160_eq_dec (x y: header 160) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_160 =>
    match y with
    | buf_160 => left eq_refl
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
Derive Signature for header.
Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
  solve_header_eqdec_ n x y
    ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h64_eq_dec) ::
     (existT _ _ h96_eq_dec) ::
     (existT _ _ h160_eq_dec) ::
     (existT _ _ h112_eq_dec) ::
     (existT _ _ h16_eq_dec) ::
      nil).
Defined.

Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.
Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  solve_eqdec'.
Defined.
Global Instance header_finite: forall n, @Finite (header n) _ _.
  intros n; solve_indexed_finiteness n [64; 96 ; 160 ; 112 ; 16 ].
Qed.

Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
  {| enum := [
      existT _ _ buf_112
    ; existT _ _ buf_16
    ; existT _ _ buf_160
    ; existT _ _ buf_64
    ; existT _ _ buf_96
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
    st_trans := transition select (| (EHdr buf_112)[15 -- 15], (EHdr buf_112)[14 -- 14], (EHdr buf_112)[13 -- 13], (EHdr buf_112)[12 -- 12], (EHdr buf_112)[11 -- 11], (EHdr buf_112)[10 -- 10], (EHdr buf_112)[9 -- 9], (EHdr buf_112)[8 -- 8], (EHdr buf_112)[7 -- 7], (EHdr buf_112)[6 -- 6], (EHdr buf_112)[5 -- 5], (EHdr buf_112)[4 -- 4], (EHdr buf_112)[3 -- 3], (EHdr buf_112)[2 -- 2], (EHdr buf_112)[1 -- 1], (EHdr buf_112)[0 -- 0], (EHdr buf_112)[111 -- 111], (EHdr buf_112)[110 -- 110], (EHdr buf_112)[109 -- 109], (EHdr buf_112)[108 -- 108], (EHdr buf_112)[107 -- 107], (EHdr buf_112)[106 -- 106], (EHdr buf_112)[105 -- 105], (EHdr buf_112)[104 -- 104], (EHdr buf_112)[103 -- 103], (EHdr buf_112)[102 -- 102], (EHdr buf_112)[101 -- 101], (EHdr buf_112)[100 -- 100], (EHdr buf_112)[99 -- 99], (EHdr buf_112)[98 -- 98], (EHdr buf_112)[97 -- 97], (EHdr buf_112)[96 -- 96]|) {{
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0 |] ==> inl State_0_suff_0 ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0 |] ==> inl State_0_suff_1 ;;;
      reject
    }}
  |}
  | State_0_suff_0 => {|
    st_op := extract(buf_160);
    st_trans := transition accept;
  |}
  | State_0_suff_1 => {|
    st_op := extract(buf_16);
    st_trans := transition inl State_1;
  |}
  | State_1 => {|
    st_op := extract(buf_112);
    st_trans := transition select (| (EHdr buf_112)[15 -- 15], (EHdr buf_112)[14 -- 14], (EHdr buf_112)[13 -- 13], (EHdr buf_112)[12 -- 12], (EHdr buf_112)[11 -- 11], (EHdr buf_112)[10 -- 10], (EHdr buf_112)[9 -- 9], (EHdr buf_112)[8 -- 8], (EHdr buf_112)[7 -- 7], (EHdr buf_112)[6 -- 6], (EHdr buf_112)[5 -- 5], (EHdr buf_112)[4 -- 4], (EHdr buf_112)[3 -- 3], (EHdr buf_112)[2 -- 2], (EHdr buf_112)[1 -- 1], (EHdr buf_112)[0 -- 0], (EHdr buf_112)[111 -- 111], (EHdr buf_112)[110 -- 110], (EHdr buf_112)[109 -- 109], (EHdr buf_112)[108 -- 108], (EHdr buf_112)[107 -- 107], (EHdr buf_112)[106 -- 106], (EHdr buf_112)[105 -- 105], (EHdr buf_112)[104 -- 104], (EHdr buf_112)[103 -- 103], (EHdr buf_112)[102 -- 102], (EHdr buf_112)[101 -- 101], (EHdr buf_112)[100 -- 100], (EHdr buf_112)[99 -- 99], (EHdr buf_112)[98 -- 98], (EHdr buf_112)[97 -- 97], (EHdr buf_112)[96 -- 96]|) {{
      [| exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_1_suff_0 ;;;
      [| exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0 |] ==> inl State_1_suff_1 ;;;
      reject
    }}
  |}
  | State_1_suff_0 => {|
    st_op := extract(buf_64);
    st_trans := transition accept;
  |}
  | State_1_suff_1 => {|
    st_op := extract(buf_96);
    st_trans := transition accept;
  |}
end.
Program Definition aut: Syntax.t state header :=
  {| t_states := states |}.
Solve Obligations with (destruct s; cbv; Lia.lia).
End Optimized.