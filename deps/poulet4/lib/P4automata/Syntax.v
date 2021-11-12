Require Coq.Lists.List.
Import List.ListNotations.
Require Coq.Logic.Eqdep_dec.
Require Import Coq.Classes.EquivDec.
Require Import Equations.Prop.EqDecInstances.
Require Import Coq.Program.Program.
Require Import Poulet4.HAList.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Ntuple.
Require Poulet4.P4automata.DepEnv.
Require Poulet4.P4automata.P4automaton.
Module P4A := P4automaton.

Module Env := Poulet4.P4automata.DepEnv.

Open Scope list_scope.

Section Syntax.

  Set Implicit Arguments.

  (* State identifiers. *)
  Variable (S: Type).
  Context `{S_eq_dec: EquivDec.EqDec S eq}.
  Context `{S_finite: @Finite S _ S_eq_dec}.

  (* Typed header identifiers. *)
  Variable (H: nat -> Type).
  Definition H' := {n: nat & H n}.
  Context `{H'_eq_dec: EquivDec.EqDec H' eq}.
  Context `{H'_finite: @Finite H' _ H'_eq_dec}.

  Global Instance H_eq_dec: forall n, EquivDec.EqDec (H n) eq.
  Proof.
    unfold EquivDec.EqDec; intros.
    destruct (H'_eq_dec (existT _ n x) (existT _ n y)).
    - apply Eqdep_dec.inj_pair2_eq_dec in e;
        auto using PeanoNat.Nat.eq_dec.
    - right; intro; apply c.
      now rewrite H0.
  Defined.

  Inductive hdr_ref: Type :=
  | HRVar (var: H').
  (*| HRField (hdr: hdr_ref) (field: string).*)
  Derive NoConfusion for hdr_ref.
  Global Program Instance hdr_ref_eq_dec : EquivDec.EqDec hdr_ref eq :=
    { equiv_dec x y :=
        match x, y with
        | @HRVar x, @HRVar y =>
          if x == y then in_left else in_right
        end }.
  Solve Obligations with unfold equiv, complement in *;
    program_simpl; congruence.

  Inductive expr : nat -> Type :=
  | EHdr {n} (h: H n): expr n
  | ELit {n} (bs: n_tuple bool n): expr n
  | ESlice {n} (e: expr n) (hi lo: nat): expr (Nat.min (1 + hi) n - lo)
  | EConcat {n m} (l: expr n) (r: expr m): expr (n + m).
  (* todo: binops, ...? *)

  Definition state_ref: Type := S + bool.

  Inductive v n :=
  | VBits: n_tuple bool n -> v n.

  Global Program Instance v_eq_dec (n: nat): EquivDec.EqDec (v n) eq :=
    { equiv_dec x y :=
        match x, y with
        | VBits _ xs, VBits _ ys =>
          if xs == ys
          then in_left
          else in_right
        end }.
  Solve All Obligations with unfold equiv, complement in *;
    program_simpl; congruence.

  Global Program Instance v_finite (n: nat): Finite (v n) :=
    {| enum := List.map (VBits n) (enum (n_tuple bool n)) |}.
  Next Obligation.
    apply NoDup_map.
    - intros x y Heq; inversion Heq; auto.
    - eapply NtupleProofs.BoolTupleFinite.
  Qed.
  Next Obligation.
    destruct x.
    rewrite List.in_map_iff.
    eexists; intuition eauto.
    eapply NtupleProofs.BoolTupleFinite.
  Qed.

  Inductive typ :=
  | TBits (n: nat)
  | TPair (t1 t2: typ).
  Derive NoConfusion for typ.

  Inductive pat: typ -> Type :=
  | PExact {n} (val: v n) : pat (TBits n)
  | PAny: forall n, pat (TBits n)
  | PPair {t1 t2} (p1: pat t1) (p2: pat t2) : pat (TPair t1 t2).
  Derive Signature for pat.

  Inductive cond: typ -> Type :=
  | CExpr {n} (e: expr n) : cond (TBits n)
  | CPair {t1 t2} (c1: cond t1) (c2: cond t2) : cond (TPair t1 t2).
  Derive Signature for cond.

  Record sel_case t: Type :=
    { sc_pat: pat t;
      sc_st: state_ref }.

  Inductive transition: Type :=
  | TGoto (state: state_ref)
  | TSel {t} (c: cond t) (cases: list (sel_case t)) (default: state_ref).

  Inductive op: nat -> Type :=
  | OpNil: op 0
  | OpSeq {n1 n2} (o1: op n1) (o2: op n2): op (n1 + n2)
  | OpExtract (hdr: H'): op (projT1 hdr)
  | OpAsgn {n} (lhs: H n) (rhs: expr n): op 0.

  Definition op_size {n} (o: op n) := n.

  Fixpoint nonempty {n} (o: op n) : Prop :=
    match o with
    | OpAsgn _ _
    | OpNil => True
    | OpSeq o1 o2 => nonempty o1 /\ nonempty o2
    | OpExtract hdr => projT1 hdr > 0
    end.

  Record state: Type :=
    { st_size: nat;
      st_op: op st_size;
      st_trans: transition }.

  Definition state_size (st: state) : nat :=
    st_size st.

  Record t: Type :=
    { t_states: S -> state;
      t_nonempty: forall s, nonempty (t_states s).(st_op);
      t_has_extract: forall s, state_size (t_states s) > 0 }.

  Program Definition bind (s: S) (st: state) (ex: state_size st > 0) (ok: nonempty st.(st_op)) (a: t) :=
    {| t_states := fun s' => if s == s' then st else a.(t_states) s' |}.
  Next Obligation.
    destruct (s == s0).
    - auto.
    - eapply a.(t_nonempty).
  Qed.
  Next Obligation.
    destruct (s == s0).
    - auto.
    - eapply a.(t_has_extract).
  Qed.

  Definition size (a: t) (s: S) :=
    state_size (a.(t_states) s).

  Lemma eq_dec_refl (A: Type) (eq_dec: forall x y : A, {x = y} + {x <> y}) :
    forall x,
      eq_dec x x = left eq_refl.
  Proof using.
    intros.
    pose proof (@Eqdep_dec.UIP_dec A eq_dec x x eq_refl).
    destruct (eq_dec x x).
    - erewrite H0; eauto.
    - congruence.
  Qed.
  Hint Rewrite eq_dec_refl : core.

End Syntax.

Section Fmap.
  Set Implicit Arguments.
  Variables (S1 S2: Type).
  Variables (H1 H2: nat -> Type).
  Variable (f: S1 -> S2).
  Variable (g: forall n, H1 n -> H2 n).

  Definition sigma_fmapH (h: H' H1) : H' H2 :=
    existT _ (projT1 h) (g (projT2 h)).

  Definition hdr_ref_fmapH (h: hdr_ref H1) : hdr_ref H2 :=
    match h with
    | HRVar h => HRVar (sigma_fmapH h)
    end.

  Fixpoint expr_fmapH {n} (e: expr H1 n) : expr H2 n :=
    match e with
    | EHdr _ h => EHdr _ (g h)
    | ELit _ bs => ELit _ bs
    | ESlice e hi lo => ESlice (expr_fmapH e) hi lo
    | EConcat l r => EConcat (expr_fmapH l) (expr_fmapH r)
    end.

  Definition state_ref_fmapS (s: state_ref S1) : state_ref S2 :=
    match s with
    | inl s' => inl (f s')
    | inr r => inr r
    end.

  Definition sel_case_fmapS {t} (c: sel_case S1 t) : sel_case S2 t :=
    {| sc_pat := c.(sc_pat);
       sc_st := state_ref_fmapS c.(sc_st) |}.

  Fixpoint cond_fmapH {t} (c: cond H1 t) : cond H2 t :=
    match c with
    | @CExpr _ n e => CExpr (expr_fmapH e)
    | @CPair _ t1 t2 c1 c2 => CPair (cond_fmapH c1) (cond_fmapH c2)
    end.

  Definition transition_fmapSH (t: transition S1 H1) : transition S2 H2 :=
    match t with
    | TGoto _ s => TGoto _ (state_ref_fmapS s)
    | TSel cond cases default =>
      TSel (cond_fmapH cond) (List.map sel_case_fmapS cases) (state_ref_fmapS default)
    end.

  Fixpoint op_fmapH {n} (o: op H1 n) : op H2 n :=
    match o with
    | OpNil _ => OpNil _
    | OpSeq o1 o2 => OpSeq (op_fmapH o1) (op_fmapH o2)
    | OpExtract hdr => OpExtract (sigma_fmapH hdr)
    | OpAsgn lhs rhs => OpAsgn (g lhs) (expr_fmapH rhs)
    end.

  Definition state_fmapSH (s: state S1 H1) : state S2 H2 :=
    {| st_size := s.(st_size);
       st_op := op_fmapH s.(st_op);
       st_trans := transition_fmapSH s.(st_trans) |}.

  Lemma state_fmapSH_size :
    forall s,
      state_size (state_fmapSH s) = state_size s.
  Proof.
    tauto.
  Qed.

  Lemma op_fmapH_nonempty :
    forall n (o: op H1 n),
      nonempty (op_fmapH o) <-> nonempty o.
  Proof.
    induction o; simpl; intuition.
  Qed.

End Fmap.

Section Interp.
  Unset Implicit Arguments.
  (* State identifiers. *)
  Variable (S: Type).
  Context `{S_eqdec: EquivDec.EqDec S eq}.

  (* Header identifiers. *)
  Variable (H: nat -> Type).
  Context `{H'_eq_dec: EquivDec.EqDec (H' H) eq}.

  Variable (a: t S H).

  Definition store := Env.t nat H v.

  Definition clamp_list (n: nat) (l: list bool) :=
    List.firstn n (l ++ (List.repeat false (List.length l - n))).

  Definition assign {n} (h: H n) (v: v n) (st: store) : store :=
    Env.bind _ _ _ h v st.

  Definition find {n} (h: H n) (st: store) : v n :=
    match Env.find _ _ _ h st with
    | Some v => v
    | None => VBits _ (n_tuple_repeat _ false)
    end.

  Definition slice {A} (l: list A) (hi lo: nat) :=
    List.skipn lo (List.firstn (1 + hi) l).

  Lemma slice_len:
    forall A hi lo (l: list A),
      length (slice l hi lo) = Nat.min (1 + hi) (length l) - lo.
  Proof.
    unfold slice.
    intros.
    rewrite List.skipn_length.
    rewrite List.firstn_length.
    reflexivity.
  Qed.

  Equations eval_expr (n: nat) (st: store) (e: expr H n) : v n :=
    { eval_expr n st (EHdr n h) := find h st;
      eval_expr n st (ELit _ bs) := VBits _ bs;
      eval_expr n st (ESlice e hi lo) :=
        let '(VBits _ bs) := eval_expr _ st e in
        VBits _ (n_tuple_slice hi lo bs);
      eval_expr n st (EConcat l r) :=
        let '(VBits _ bs_l) := eval_expr _ st l in
        let '(VBits _ bs_r) := eval_expr _ st r in
        VBits _ (n_tuple_concat bs_l bs_r)
    }.

  Program Definition extract {A} (excess n: nat) (l: n_tuple A (excess + n)) : n_tuple A n :=
    rewrite_size _ (n_tuple_skip_n excess l).
  Next Obligation.
    Lia.lia.
  Qed.

  Equations eval_op {sz: nat} (st: store) (bits: n_tuple bool sz) (o: op H sz) : store :=
    {
      eval_op st bits (OpNil _) :=
        st;
      eval_op st bits (OpExtract hdr) :=
        assign (projT2 hdr) (VBits _ bits) st;
      eval_op st bits (OpSeq o1 o2) :=
        let bits' := n_tuple_take_n (op_size o1) bits in
        let st := eval_op st (rewrite_size _ bits') o1 in
        eval_op st (rewrite_size _ (n_tuple_skip_n (op_size o1) bits)) o2;
      eval_op st bits (OpAsgn hdr expr) :=
        assign hdr (eval_expr _ st expr) st
    }.
  Next Obligation.
    unfold op_size.
    Lia.lia.
  Qed.
  Next Obligation.
    unfold op_size.
    Lia.lia.
  Qed.

  Definition update
    (state: S)
    (bits: n_tuple bool (st_size (t_states a state)))
    (st: store)
    : store :=
    eval_op st
            (* Deal with conversion of n-tuple to (n+0)-tuple *)
            (eq_rect _ _ bits _ (plus_O_n _))
            (a.(t_states) state).(st_op).

  Equations match_pat {T: typ} (st: store) (c: cond H T) (p: pat T) : bool := {
    match_pat st (CExpr e) (PExact val) :=
      if eval_expr _ st e == val then true else false;
    match_pat st (CExpr e) (PAny _) :=
      true;
    match_pat st (CPair c1 c2) (PPair p1 p2) =>
      andb (match_pat st c1 p1) (match_pat st c2 p2)
  }.

  Fixpoint eval_sel
    {T: typ}
    (st: store)
    (c: cond H T)
    (cases: list (sel_case S T))
    (default: state_ref S)
    : state_ref S :=
    match cases with
    | sc::cases =>
      if match_pat st c sc.(sc_pat)
      then sc.(sc_st)
      else eval_sel st c cases default
    | nil => default
    end.

  Definition eval_trans (st: store) (t: transition S H) : state_ref S :=
    match t with
    | TGoto _ state => state
    | TSel cond cases default =>
      eval_sel st cond cases default
    end.

  Definition transitions (s: S) (st: store) : state_ref S :=
    eval_trans st (a.(t_states) s).(st_trans).

  Definition possible_next_states (st: state S H) : list (state_ref S) :=
    match st.(st_trans) with
    | TGoto _ s' =>
      [s']
    | TSel _ cases default =>
      default :: List.map (fun c => sc_st c) cases
    end.

  Definition interp : P4A.p4automaton :=
    {| P4A.store := store;
       P4A.states := S;
       P4A.size := size a;
       P4A.update := update;
       P4A.transitions := transitions;
       P4A.cap := a.(t_has_extract) |}.
End Interp.
Arguments EHdr {_ _} _.
Arguments ELit {_ _} _.
Arguments ESlice {_ _} _ _ _.
Arguments interp {_ _ _ _} a.

Section Inline.
  (* State identifiers. *)
  Variable (S: Type).
  Context `{S_eq_dec: EquivDec.EqDec S eq}.

  (* Header identifiers. *)
  Variable (H: nat -> Type).

  Program Definition inline (pref: S) (suff: S) (auto: t S H) : t S H :=
    match auto.(t_states) pref with
    | Build_state op (TGoto _ (inl nxt)) =>
      if nxt == suff
      then
      let pref' :=
        match auto.(t_states) suff with
        | suff_st => {| st_op := OpSeq op (st_op suff_st); st_trans := st_trans suff_st |}
        end in
      bind pref pref' _ _ auto
      else auto
    | _ => auto
    end.
  Next Obligation.
    pose proof auto.(t_has_extract) suff.
    unfold state_size in *.
    simpl in *.
    Lia.lia.
  Qed.
  Next Obligation.
    pose proof auto.(t_nonempty) suff.
    pose proof auto.(t_nonempty) pref.
    rewrite <- Heq_anonymous in * |-.
    simpl in *.
    intuition.
  Qed.

  (* Lemma inline_corr :
    forall pref suff auto (s: store),
      let start_config : P4A.configuration (interp _ _ auto) := (SNStart, s, nil) in
      True. *)

End Inline.

Section Properties.

  (* State identifiers. *)
  Variable (S1: Type).
  Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
  Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

  Variable (S2: Type).
  Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
  Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

  Notation S := ((S1 + S2)%type).

  (* Header identifiers. *)
  Variable (H: nat -> Type).
  Context `{H_eq_dec: forall n, EquivDec.EqDec (H n) eq}.
  Context `{H'_eq_dec: EquivDec.EqDec (H' H) eq}.
  Context `{H_finite: @Finite (H' H) _ H'_eq_dec}.

  Variable (a: t S H).

  Import P4A.

  Lemma conf_state_step_transition_syntactic
    (q: P4A.configuration (interp a))
    (b: bool)
    (s: S)
  :
    conf_state q = inl s ->
    1 + conf_buf_len q = size' (interp a) (conf_state q) ->
    List.In (conf_state (step q b))
            (possible_next_states _ _ (t_states a s)).
  Proof.
    intros.
    rewrite conf_state_step_transition with (Heq := H1).
    destruct (conf_state q); [|discriminate].
    autorewrite with update'.
    autorewrite with transitions'.
    simpl.
    unfold Syntax.transitions.
    unfold Syntax.eval_trans.
    inversion H0; subst.
    unfold possible_next_states.
    destruct (st_trans _).
    - apply List.in_eq.
    - induction cases.
      + simpl; now left.
      + simpl eval_sel.
        rewrite List.map_cons.
        destruct (match_pat _ _ _ _).
        * apply List.in_cons.
          apply List.in_eq.
        * destruct IHcases.
          -- rewrite H2 at 2.
             apply List.in_eq.
          -- now repeat apply List.in_cons.
  Qed.


  Lemma conf_state_follow_transition_syntactic
    (q: configuration (interp a))
    (bs: list bool)
    (s: S)
  :
    conf_state q = inl s ->
    length bs + conf_buf_len q = size' (interp a) (conf_state q) ->
    List.In (conf_state (follow q bs))
            (possible_next_states _ _ (t_states a s)).
  Proof.
    revert q; induction bs; intros.
    - simpl in H1.
      pose proof (conf_buf_sane q).
      Lia.lia.
    - destruct bs; simpl in *.
      + autorewrite with follow.
        now apply conf_state_step_transition_syntactic.
      + rewrite follow_equation_2.
        apply IHbs.
        * rewrite conf_state_step_fill; auto; Lia.lia.
        * rewrite conf_buf_len_step_fill; try Lia.lia.
          rewrite conf_state_step_fill; Lia.lia.
  Qed.

End Properties.
