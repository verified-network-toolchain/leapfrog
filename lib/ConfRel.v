From Equations Require Import Equations.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.

Require Import Leapfrog.Classes.

Require Import Coq.Program.Program.
Import ListNotations.

Require Import Leapfrog.Relations.
Require Import Leapfrog.FinType.
Require Import Leapfrog.P4automaton.
Require Import Leapfrog.Ntuple.
Require Leapfrog.Syntax.
Module P4A := Leapfrog.Syntax.

Open Scope list_scope.

Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.

Lemma split_ex:
  forall A B (P: A * B -> Prop),
    (exists x: A, exists y: B, P (x, y)) <->
    exists x: A * B, P x.
Proof.
  firstorder.
  destruct x.
  firstorder.
Qed.

(* Bitstring variable context. *)
Inductive bctx :=
| BCEmp: bctx
| BCSnoc: bctx -> N -> bctx.
Derive NoConfusion for bctx.
Fixpoint bctx_eqd (x: bctx) (y: bctx) : ({x = y} + {x <> y})%type.
refine (
  match x, y with 
  | BCEmp, BCEmp => left eq_refl
  | BCSnoc x' n, BCSnoc y' m => 
    match bctx_eqd x' y', N.eq_dec n m with 
    | left H, left H' => left _
    | _, _ => right _
    end
  | _, _ => right _
  end
); intros; congruence.
Defined.

Derive EqDec for bctx.

Global Instance bctx_eq_dec : EquivDec.EqDec bctx eq := bctx_eqdec.

(* Bitstring variable valuation. *)
Fixpoint bval (c: bctx) : Type :=
  match c with
  | BCEmp => unit
  | BCSnoc c' size => bval c' * n_tuple bool size
  end.

Inductive bvar : bctx -> Type :=
| BVarTop:
    forall c size,
      bvar (BCSnoc c size)
| BVarRest:
    forall c size,
      bvar c ->
      bvar (BCSnoc c size).
Arguments BVarRest {_ _} _.
Derive NoConfusion Signature for bvar.

Definition weaken_bvar {c} (size: N) : bvar c -> bvar (BCSnoc c size) :=
  @BVarRest c size.

Equations bvar_eqdec {c} (x y: bvar c) : {x = y} + {x <> y} :=
  { bvar_eqdec (BVarTop _ _) (BVarTop _ _) := in_left;
    bvar_eqdec (BVarRest x') (BVarRest y') := if bvar_eqdec x' y'
                                              then in_left
                                              else in_right;
    bvar_eqdec _ _ := in_right }.
Next Obligation.
  contradict n.
  apply Eqdep_dec.inj_pair2_eq_dec.
  - apply bctx_eq_dec.
  - now inversion n.
Qed.
#[global] Transparent bvar_eqdec.

Global Instance bvar_eq_dec {c}: EquivDec.EqDec (bvar c) eq := bvar_eqdec.

Fixpoint check_bvar {c} (x: bvar c) : N :=
  match x with
  | BVarTop c size => size
  | BVarRest x' => check_bvar x'
  end.

Equations interp_bvar {c} (valu: bval c) (x: bvar c) : n_tuple bool (check_bvar x) :=
  { interp_bvar (_, bs)    (BVarTop _ _) := bs;
    interp_bvar (valu', bs) (BVarRest x') := interp_bvar valu' x' }.

Section ConfRel.
  Set Implicit Arguments.

  (* State identifiers. *)
  Variable (St: Type).
  Context `{St_eq_dec: EquivDec.EqDec St eq}.
  Context `{St_finite: @Finite St _ St_eq_dec}.

  (* Header identifiers. *)
  Variable (Hdr: Type).
  Context `{Hdr_eq_dec: EquivDec.EqDec Hdr eq}.
  Context `{Hdr_finite: @Finite Hdr _ Hdr_eq_dec}.
  Variable (Hdr_sz: Hdr -> N).

  Variable (a: P4A.t St Hdr_sz).

  Notation conf := (configuration (P4A.interp a)).

  Record state_template :=
    { st_state: state_ref (P4A.interp a);
      st_buf_len: N }.

  Definition state_template_sane (st: state_template) :=
    (st.(st_buf_len) < (size' (P4A.interp a) st.(st_state)))%N.

  Definition state_template_sane_fn (st: state_template) :=
    match N.ltb st.(st_buf_len) (size' (P4A.interp a) st.(st_state)) with
    | true => True
    | false => False
    end.

  Lemma state_template_sane_fn_equiv:
    forall st,
      state_template_sane st <->
      state_template_sane_fn st.
  Proof.
    unfold state_template_sane, state_template_sane_fn.
    intros st.
    destruct ((st_buf_len st <? size' (P4A.interp a) (st_state st))%N) eqn:?.
    - now rewrite N.ltb_lt in Heqb.
    - now rewrite N.ltb_nlt in Heqb.
  Qed.
    (* pose proof (PeanoNat.Nat.ltb_spec0 (st_buf_len st) (size' _ (st_state st))).
    destruct H; eauto.
    - tauto.
    - tauto.
  Qed. *)

  Global Program Instance state_template_eq_dec : EquivDec.EqDec state_template eq :=
    { equiv_dec x y :=
        if x.(st_state) == y.(st_state)
        then if x.(st_buf_len) == y.(st_buf_len)
             then in_left
             else in_right
        else in_right }.
  Solve Obligations with (destruct x, y;
                           unfold equiv, complement in *;
                           simpl in *;
                           congruence).

  Definition interp_state_template (st: state_template) (c: conf) :=
    st.(st_state) = c.(conf_state) /\
    st.(st_buf_len) = c.(conf_buf_len).

  Lemma interp_state_template_dichotomy (t1 t2: state_template) (c: conf):
    interp_state_template t1 c ->
    interp_state_template t2 c ->
    t1 = t2.
  Proof.
    unfold interp_state_template; intros.
    destruct H, H0.
    destruct t1, t2; simpl in *.
    congruence.
  Qed.

  Fixpoint interp_tpairs (sts: list (state_template * state_template)) (q1 q2: conf) : Prop :=
    match sts with
    | [] =>
      False
    | (st1, st2) :: sts =>
      (interp_state_template st1 q1 /\
       interp_state_template st2 q2)
      \/ interp_tpairs sts q1 q2
    end.

  Inductive side := Left | Right.
  Derive NoConfusion for side.
  Derive EqDec for side.

  Inductive bit_expr (c: bctx) :=
  | BELit (l: list bool)
  | BEBuf (a: side)
  | BEHdr (a: side) (h: P4A.hdr_ref Hdr)
  | BEVar (b: bvar c)
  | BESlice (e: bit_expr c) (hi lo: N)
  | BEConcat (e1 e2: bit_expr c).
  Arguments BELit {c} _.
  Arguments BEBuf {c} _.
  Arguments BEHdr {c} _ _.
  Derive NoConfusion for bit_expr.

  Definition beslice {c} (be: bit_expr c) (hi lo: N) :=
    (* if Nat.ltb hi lo then BELit [] else *)
    match be with
    | BELit l => BELit (Ntuple.slice l hi lo)
    | BESlice x hi' lo' => BESlice x (N.min (lo' + hi) hi') (lo' + lo)
    | _ => BESlice be hi lo
    end.

  Definition beconcat {c} (l: bit_expr c) (r: bit_expr c) :=
    match l, r with
    | BELit l, BELit r => BELit (l ++ r)
    | _, _ => BEConcat l r
    end.

  Fixpoint weaken_bit_expr {c} (size: N) (b: bit_expr c) : bit_expr (BCSnoc c size) :=
    match b with
    | BELit l => BELit l
    | BEBuf a => BEBuf a
    | BEHdr a h => BEHdr a h
    | BEVar b => BEVar (weaken_bvar size b)
    | BESlice e hi lo => BESlice (weaken_bit_expr size e) hi lo
    | BEConcat e1 e2 => BEConcat (weaken_bit_expr size e1) (weaken_bit_expr size e2)
    end.

  Obligation Tactic := intros.
  Unset Transparent Obligations.
  Equations bit_expr_eq_dec {c: bctx} : forall x y: bit_expr c, {x = y} + {x <> y} :=
    { bit_expr_eq_dec (BELit l) (BELit l') :=
        if l == l' then in_left else in_right;
      bit_expr_eq_dec (BEBuf a) (BEBuf a') :=
        if side_eqdec a a' then in_left else in_right;
      bit_expr_eq_dec (BEHdr a h) (BEHdr a' h') :=
        if Sumbool.sumbool_and _ _ _ _ (side_eqdec a a') (h == h')
        then in_left
        else in_right;
      bit_expr_eq_dec (BEVar x) (BEVar x') :=
        if bvar_eq_dec x x'
        then in_left
        else in_right;
      bit_expr_eq_dec (BESlice e hi lo) (BESlice e' hi' lo') :=
        if Sumbool.sumbool_and _ _ _ _ (hi == hi') (lo == lo')
        then if bit_expr_eq_dec e e'
             then in_left
             else in_right
        else in_right;
      bit_expr_eq_dec (BEConcat e1 e2) (BEConcat e1' e2') :=
        if bit_expr_eq_dec e1 e1'
        then if bit_expr_eq_dec e2 e2'
             then in_left
             else in_right
        else in_right;
             bit_expr_eq_dec _ _ := in_right }.

  Solve All Obligations with
      (intros;
      repeat match goal with
             | H: _ /\ _|- _ => destruct H
             | H: _ \/ _ |- _ => destruct H
             | |- ?g => congruence
             end).
  Next Obligation.
  exact 0%N.
  Defined.
  #[global] Transparent bit_expr_eq_dec.

  Global Program Instance bit_expr_eqdec {c} : EquivDec.EqDec (bit_expr c) eq :=
    { equiv_dec := bit_expr_eq_dec }.

  Fixpoint be_size {c} b1 b2 (e: bit_expr c) : N :=
    match e with
    | BELit l => N.of_nat (List.length l)
    | BEBuf side =>
      match side with
      | Left => b1
      | Right => b2
      end
    | BEHdr a (P4A.HRVar h) => Hdr_sz h
    | BEVar x => check_bvar x
    | BESlice e hi lo =>
      N.min (1 + hi) (be_size b1 b2 e) - lo
    | BEConcat e1 e2 =>
      be_size b1 b2 e1 + be_size b1 b2 e2
    end.

  Equations interp_bit_expr {b1 b2 c}
    (e: bit_expr c)
    (valu: bval c)
    (buf1: n_tuple bool b1)
    (buf2: n_tuple bool b2)
    (store1 store2: store (P4A.interp a))
    : n_tuple bool (be_size b1 b2 e)
  := {
    interp_bit_expr (BELit l) valu buf1 buf2 store1 store2 :=
      l2t l;
    interp_bit_expr (BEBuf Left) valu buf1 buf2 store1 store2 :=
      buf1;
    interp_bit_expr (BEBuf Right) valu buf1 buf2 store1 store2 :=
      buf2;
    interp_bit_expr (BEHdr a h) valu buf1 buf2 store1 store2 :=
      let store := match a with
               | Left => store1
               | Right => store2
               end
      in
      match h with
      | P4A.HRVar var =>
        match P4A.find _ _ var store  with
        | P4A.VBits v => v
        end
      end;
    interp_bit_expr (BEVar x) valu buf1 buf2 store1 store2 :=
      interp_bvar valu x;
    interp_bit_expr (BESlice e hi lo) valu buf1 buf2 store1 store2 :=
      n_tuple_slice hi lo (interp_bit_expr e valu buf1 buf2 store1 store2);
    interp_bit_expr (BEConcat e1 e2) valu buf1 buf2 store1 store2 :=
      n_tuple_concat
        (interp_bit_expr e1 valu buf1 buf2 store1 store2)
        (interp_bit_expr e2 valu buf1 buf2 store1 store2)
  }.

  Inductive store_rel c :=
  | BRTrue
  | BRFalse
  | BREq (e1 e2: bit_expr c)
  | BRAnd (r1 r2: store_rel c)
  | BROr (r1 r2: store_rel c)
  | BRImpl (r1 r2: store_rel c).
  Arguments store_rel : default implicits.

  (* smart constructors *)

  Definition brand {c} (l: store_rel c) (r: store_rel c) :=
    (* BRAnd l r. *)
    match l with
    | BRTrue _ => r
    | BRFalse _ => BRFalse c
    | _ =>
      match r with
      | BRTrue _ => l
      | BRFalse _ => BRFalse c
      | _ => BRAnd l r
      end
    end.

  Definition bror {c} (l: store_rel c) (r: store_rel c) :=
    (* BROr l r. *)
    match l with
    | BRTrue _ => BRTrue c
    | BRFalse _ => r
    | _ =>
      match r with
      | BRTrue _ => BRTrue c
      | BRFalse _ => l
      | _ => BROr l r
      end
    end.

  Definition brimpl {c} (l: store_rel c) (r: store_rel c) :=
    (* BRImpl l r. *)
    match l with
    | BRTrue _ => r
    | BRFalse _ => BRTrue c
    | _ =>
      match r with
      | BRTrue _ => BRTrue c
      | _ => BRImpl l r
      end
    end.

  Equations store_rel_eq_dec {c: bctx} : forall x y: store_rel c, {x = y} + {x <> y} :=
    { store_rel_eq_dec (BRTrue _) (BRTrue _) := in_left;
      store_rel_eq_dec (BRFalse _) (BRFalse _) := in_left;
      store_rel_eq_dec (BREq e11 e12) (BREq e21 e22) :=
        if Sumbool.sumbool_and _ _ _ _ (e11 == e21) (e12 == e22)
        then in_left
        else in_right;
      store_rel_eq_dec (BRAnd r11 r12) (BRAnd r21 r22) :=
        if (store_rel_eq_dec r11 r21)
        then if (store_rel_eq_dec r12 r22)
             then in_left
             else in_right
        else in_right;
      store_rel_eq_dec (BROr r11 r12) (BROr r21 r22) :=
        if (store_rel_eq_dec r11 r21)
        then if (store_rel_eq_dec r12 r22)
             then in_left
             else in_right
        else in_right;
      store_rel_eq_dec (BRImpl r11 r12) (BRImpl r21 r22) :=
        if (store_rel_eq_dec r11 r21)
        then if (store_rel_eq_dec r12 r22)
             then in_left
             else in_right
        else in_right;
    store_rel_eq_dec _ _ := in_right }.

  Solve All Obligations with
      (intros;
      repeat match goal with
             | H: _ /\ _|- _ => destruct H
             | H: _ \/ _ |- _ => destruct H
             | |- ?g => congruence
             end).
  #[global] Transparent store_rel_eq_dec.

  Global Program Instance store_rel_eqdec {c: bctx}: EquivDec.EqDec (store_rel c) eq :=
    store_rel_eq_dec.

  Fixpoint weaken_store_rel {c} (size: N) (r: store_rel c) : store_rel (BCSnoc c size) :=
    match r with
    | BRTrue _ => BRTrue _
    | BRFalse _ => BRFalse _
    | BREq e1 e2 => BREq (weaken_bit_expr size e1) (weaken_bit_expr size e2)
    | BRAnd r1 r2 => brand (weaken_store_rel size r1) (weaken_store_rel size r2)
    | BROr r1 r2 => bror (weaken_store_rel size r1) (weaken_store_rel size r2)
    | BRImpl r1 r2 => BRImpl (weaken_store_rel size r1) (weaken_store_rel size r2)
    end.

  Equations interp_store_rel {b1 b2 c}
    (r: store_rel c)
    (valu: bval c)
    (buf1: n_tuple bool b1)
    (buf2: n_tuple bool b2)
    (store1 store2: store (P4A.interp a))
    : Prop := {
    interp_store_rel (BRTrue _) valu buf1 buf2 store1 store2 :=
      True;
    interp_store_rel (BRFalse _) valu buf1 buf2 store1 store2 :=
      False;
    interp_store_rel (BREq e1 e2) valu buf1 buf2 store1 store2 :=
      match eq_dec (be_size b1 b2 e1) (be_size b1 b2 e2) with
      | left Heq =>
        eq_rect _ _ (interp_bit_expr e1 valu buf1 buf2 store1 store2) _ Heq =
        interp_bit_expr e2 valu buf1 buf2 store1 store2
      | right _ => False
      end;
    interp_store_rel (BRAnd r1 r2) valu buf1 buf2 store1 store2 :=
      interp_store_rel r1 valu buf1 buf2 store1 store2 /\
      interp_store_rel r2 valu buf1 buf2 store1 store2;
    interp_store_rel (BROr r1 r2) valu buf1 buf2 store1 store2 :=
      interp_store_rel r1 valu buf1 buf2 store1 store2 \/
      interp_store_rel r2 valu buf1 buf2 store1 store2;
    interp_store_rel (BRImpl r1 r2) valu buf1 buf2 store1 store2 :=
      interp_store_rel r1 valu buf1 buf2 store1 store2 ->
      interp_store_rel r2 valu buf1 buf2 store1 store2
  }.

  (* correctness of smart constructors *)
  Lemma bror_corr :
    forall c (l r: store_rel c) v
           b1 b2 (buf1: n_tuple bool b1) (buf2: n_tuple bool b2)
           store1 store2,
        interp_store_rel (BROr l r) v buf1 buf2 store1 store2 <->
        interp_store_rel (bror l r) v buf1 buf2 store1 store2.
  Proof.
    split; intros; destruct l, r; unfold bror in *;
    autorewrite with interp_store_rel in *; auto; intuition.
  Qed.

  Lemma brand_corr :
    forall c (l r: store_rel c) v
           b1 b2 (buf1: n_tuple bool b1) (buf2: n_tuple bool b2)
           store1 store2,
        interp_store_rel (BRAnd l r) v buf1 buf2 store1 store2 <->
        interp_store_rel (brand l r) v buf1 buf2 store1 store2.
  Proof.
    split; intros; destruct l, r; unfold brand in *;
    autorewrite with interp_store_rel in *; auto; intuition.
  Qed.

  Lemma brimpl_corr :
    forall c (l r: store_rel c) v
           b1 b2 (buf1: n_tuple bool b1) (buf2: n_tuple bool b2)
           store1 store2,
        interp_store_rel (BRImpl l r) v buf1 buf2 store1 store2 <->
        interp_store_rel (brimpl l r) v buf1 buf2 store1 store2.
  Proof.
    split; intros; destruct l, r; unfold brimpl in *;
    autorewrite with interp_store_rel in *; auto; intuition.
  Qed.

  Record conf_states :=
    { cs_st1: state_template;
      cs_st2: state_template; }.
  Global Program Instance conf_states_eq_dec: EquivDec.EqDec conf_states eq :=
    { equiv_dec x y :=
        if x.(cs_st1) == y.(cs_st1)
        then if x.(cs_st2) == y.(cs_st2)
             then in_left
             else in_right
        else in_right }.
  Solve All Obligations with (destruct x, y; simpl in *; congruence).

  Record conf_rel :=
    { cr_st: conf_states;
      cr_ctx: bctx;
      cr_rel: store_rel cr_ctx }.
  Equations conf_rel_eq_dec: EquivDec.EqDec conf_rel eq :=
    { conf_rel_eq_dec x y with (bctx_eq_dec x.(cr_ctx) y.(cr_ctx)) :=
        { conf_rel_eq_dec ({| cr_st := st1;
                              cr_ctx := c;
                              cr_rel := rel1 |})
                          ({| cr_st := st2;
                              cr_ctx := c;
                              cr_rel := rel2 |})
                          (left eq_refl) :=
            if conf_states_eq_dec st1 st2
            then if store_rel_eq_dec rel1 rel2
                 then in_left
                 else in_right
            else in_right;
        conf_rel_eq_dec _ _ _ := in_right } }.
  Solve All Obligations with (try congruence).
  Next Obligation.
    intro Hs.
    inversion Hs.
    apply Eqdep_dec.inj_pair2_eq_dec in H1.
    - contradiction.
    - apply bctx_eq_dec.
  Qed.
  #[global] Transparent conf_rel_eq_dec.

  Global Program Instance conf_rel_eqdec: EquivDec.EqDec conf_rel eq :=
    conf_rel_eq_dec.

  Definition strengthen_rel (C: conf_rel) (C': conf_rel) (eq_st : C.(cr_st) = C'.(cr_st)) (eq_bctx : C.(cr_ctx) = C'.(cr_ctx)) : conf_rel :=
    {|  cr_st := C.(cr_st);
        cr_ctx := C.(cr_ctx);
        cr_rel := brand C.(cr_rel) (@eq_rect _ _ _ C'.(cr_rel) _ (eq_sym eq_bctx)) |}.

  Definition interp_conf_state (c: conf_states) : relation conf :=
    fun c1 c2 =>
      interp_state_template c.(cs_st1) c1 /\
      interp_state_template c.(cs_st2) c2.

  Lemma interp_conf_state_dichotomy (s1 s2: conf_states) (c1 c2: conf):
    interp_conf_state s1 c1 c2 ->
    interp_conf_state s2 c1 c2 ->
    s1 = s2.
  Proof.
    unfold interp_conf_state; intros.
    destruct H0, H1.
    destruct s1, s2; simpl in *; f_equal.
    - now apply interp_state_template_dichotomy with (c := c1).
    - now apply interp_state_template_dichotomy with (c := c2).
  Qed.

  Definition interp_conf_rel (phi: conf_rel) : relation conf :=
    fun x y =>
      interp_conf_state phi.(cr_st) x y ->
      forall valu,
        interp_store_rel phi.(cr_rel) valu x.(conf_buf) y.(conf_buf) x.(conf_store) y.(conf_store).

  Definition interp_conf_rel' (phi: conf_rel) : relation conf :=
    fun x y =>
      interp_conf_state phi.(cr_st) x y /\
      forall valu,
        interp_store_rel phi.(cr_rel) valu x.(conf_buf) y.(conf_buf) x.(conf_store) y.(conf_store).

  Definition crel :=
    list (conf_rel).

  Notation "⊤" := rel_true.
  Notation "x ⊓ y" := (relation_conjunction x y) (at level 40).
  Notation "⟦ x ⟧" := (interp_conf_rel x).
  Definition interp_crel i (rel: crel) : relation conf :=
    interp_rels i (List.map interp_conf_rel rel).

  Lemma interp_crel_cons
    (i: relation conf)
    (c: conf_rel)
    (cs: crel)
    (c1 c2: conf)
  :
    interp_crel i (c :: cs) c1 c2 <->
    interp_conf_rel c c1 c2 /\ interp_crel i cs c1 c2.
  Proof.
    unfold interp_crel, interp_rels.
    now cbn.
  Qed.

  Lemma interp_crel_app:
    forall R1 R2 q1 q2 top,
      interp_crel top (R1 ++ R2) q1 q2 <->
      interp_crel top R1 q1 q2 /\
      interp_crel top R2 q1 q2.
  Proof.
    intros.
    induction R1; cbn; intuition.
    induction R2; intuition.
  Qed.

  Lemma interp_rels_vs_interp_crel:
    forall q1 q2 R top,
      interp_rels top (map interp_conf_rel R) q1 q2 <->
      interp_crel top R q1 q2.
  Proof.
    induction R; intuition.
  Qed.

  Lemma interp_crel_quantify:
    forall (R: crel) (q1 q2: conf) top,
      interp_crel top R q1 q2 <->
      top q1 q2 /\ (forall phi, In phi R -> interp_conf_rel phi q1 q2).
  Proof.
    intros; induction R.
    - intuition.
    - rewrite interp_crel_cons, IHR; intuition.
      destruct H3; subst; intuition.
  Qed.

  Lemma interp_crel_nodup:
    forall (R: crel) (q1 q2: conf) top,
      interp_crel top R q1 q2 <->
      interp_crel top (nodup (conf_rel_eq_dec) R) q1 q2.
  Proof.
    intros.
    repeat rewrite interp_crel_quantify.
    now setoid_rewrite nodup_In.
  Qed.

  Fixpoint add_strengthen_crel (C: conf_rel) (CS: crel) : crel :=
    match CS with
    | [] => [C]
    | C' :: CS' =>
      match conf_states_eq_dec C.(cr_st) C'.(cr_st), bctx_eq_dec C.(cr_ctx) C'.(cr_ctx) with
      | left HST, left HC => (strengthen_rel C C' HST HC) :: CS'
      | _, _ => C' :: add_strengthen_crel C CS'
      end
    end.

  Record entailment :=
    { e_prem: crel;
      e_concl: conf_rel }.

  Definition interp_entailment (i: relation conf) (e: entailment) :=
    forall q1 q2,
      interp_crel i e.(e_prem) q1 q2 ->
      interp_conf_rel e.(e_concl) q1 q2.

  Definition interp_entailment' (i: relation conf) (e: entailment) :=
    forall q1 q2,
      i q1 q2 ->
      interp_conf_rel' e.(e_concl) q1 q2 ->
      interp_crel i e.(e_prem) q1 q2.

  Definition simplified_conf_rel := { ctx: bctx & store_rel ctx }.

  Definition interp_simplified_conf_rel
    (scr: simplified_conf_rel)
    {b1 b2}
    (buf1: n_tuple bool b1)
    (buf2: n_tuple bool b2)
    store1 store2
  :=
    forall valu, interp_store_rel (projT2 scr) valu buf1 buf2 store1 store2.

  Definition simplify_conf_rel (cr: conf_rel) :=
    existT _ cr.(cr_ctx) cr.(cr_rel).

  Lemma simplify_conf_rel_correct:
    forall cr c1 c2,
      interp_conf_rel cr c1 c2 <->
      (interp_conf_state cr.(cr_st) c1 c2 ->
       interp_simplified_conf_rel (simplify_conf_rel cr)
                                  c1.(conf_buf)
                                  c2.(conf_buf)
                                  c1.(conf_store)
                                  c2.(conf_store)).
  Proof.
    now unfold interp_simplified_conf_rel, interp_conf_rel.
  Qed.

  Lemma simplify_conf_rel_correct':
    forall cr c1 c2,
      interp_conf_rel' cr c1 c2 <->
      (interp_conf_state cr.(cr_st) c1 c2 /\
       interp_simplified_conf_rel (simplify_conf_rel cr)
                                  c1.(conf_buf)
                                  c2.(conf_buf)
                                  c1.(conf_store)
                                  c2.(conf_store)).
  Proof.
    now unfold interp_simplified_conf_rel, interp_conf_rel'.
  Qed.

  Definition simplified_crel := list simplified_conf_rel.

  Equations interp_simplified_crel
    (scrs: simplified_crel)
    {b1 b2}
    (buf1: n_tuple bool b1)
    (buf2: n_tuple bool b2)
    (store1 store2: store (P4A.interp a))
    : Prop
  := {
    interp_simplified_crel nil buf1 buf2 store1 store2 => True;
    interp_simplified_crel (scr :: scrs) buf1 buf2 store1 store2 =>
    interp_simplified_conf_rel scr buf1 buf2 store1 store2 /\
    interp_simplified_crel scrs buf1 buf2 store1 store2
  }.

  Definition simplify_crel (crs: crel) (st: conf_states) :=
    let filtered := filter (equiv_decb st ∘ cr_st) crs in
    map simplify_conf_rel filtered.

  Definition conf_to_state_template (c: conf) := {|
    st_state := conf_state c;
    st_buf_len := conf_buf_len c;
  |}.

  Lemma simplify_crel_correct (i: relation state_template) (crs: crel) (st: conf_states):
    forall q1 q2,
      interp_conf_state st q1 q2 ->
      (interp_crel (fun c1 c2 => i (conf_to_state_template c1) (conf_to_state_template c2)) crs q1 q2 <->
       (i (conf_to_state_template q1) (conf_to_state_template q2) /\
        interp_simplified_crel (simplify_crel crs st)
                               q1.(conf_buf)
                               q2.(conf_buf)
                               q1.(conf_store)
                               q2.(conf_store))).
  Proof.
    induction crs; intros.
    - autorewrite with interp_simplified_crel.
      unfold interp_crel; simpl.
      intuition.
    - rewrite interp_crel_cons.
      unfold simplify_crel.
      unfold compose; simpl.
      unfold equiv_decb at 1.
      destruct equiv_dec.
      + rewrite map_cons.
        autorewrite with interp_simplified_crel.
        rewrite filter_ext with (g := equiv_decb st ∘ cr_st) by auto.
        fold (simplify_crel crs st).
        rewrite IHcrs by auto.
        rewrite simplify_conf_rel_correct.
        rewrite <- e.
        intuition.
      + rewrite filter_ext with (g := equiv_decb st ∘ cr_st) by auto.
        fold (simplify_crel crs st).
        rewrite IHcrs by auto.
        intuition.
        unfold interp_conf_rel; intros.
        unfold Equivalence.equiv, complement in c.
        contradiction c.
        now apply interp_conf_state_dichotomy with (c1 := q1) (c2:= q2).
  Qed.

  Record simplified_entailment :=
    { se_st: conf_states;
      se_prems: simplified_crel;
      se_concl: simplified_conf_rel; }.

  Definition interp_simplified_entailment
    (i: relation state_template)
    (se: simplified_entailment)
  :=
    state_template_sane se.(se_st).(cs_st1) ->
    state_template_sane se.(se_st).(cs_st2) ->
    i se.(se_st).(cs_st1) se.(se_st).(cs_st2) ->
    forall (buf1: n_tuple bool se.(se_st).(cs_st1).(st_buf_len))
           (buf2: n_tuple bool se.(se_st).(cs_st2).(st_buf_len))
           (store1 store2: store (P4A.interp a)),
      interp_simplified_crel se.(se_prems) buf1 buf2 store1 store2 ->
      interp_simplified_conf_rel se.(se_concl) buf1 buf2 store1 store2.

  Definition interp_simplified_entailment'
    (i: relation state_template)
    (se: simplified_entailment)
  :=
    state_template_sane se.(se_st).(cs_st1) ->
    state_template_sane se.(se_st).(cs_st2) ->
    i se.(se_st).(cs_st1) se.(se_st).(cs_st2) ->
    forall (buf1: n_tuple bool se.(se_st).(cs_st1).(st_buf_len))
           (buf2: n_tuple bool se.(se_st).(cs_st2).(st_buf_len))
           (store1 store2: store (P4A.interp a)),
      interp_simplified_conf_rel se.(se_concl) buf1 buf2 store1 store2 ->
      interp_simplified_crel se.(se_prems) buf1 buf2 store1 store2.

  Definition simplify_entailment (e: entailment) :=
    {| se_st := e.(e_concl).(cr_st);
       se_prems := simplify_crel e.(e_prem) e.(e_concl).(cr_st);
       se_concl := simplify_conf_rel e.(e_concl); |}.

  Lemma simplify_entailment_correct (e: entailment):
    forall i: Relations.rel state_template,
      interp_entailment (fun c1 c2 => i (conf_to_state_template c1)
                                        (conf_to_state_template c2)) e <->
      interp_simplified_entailment i (simplify_entailment e).
  Proof.
    intros.
    unfold interp_entailment, simplify_entailment, interp_simplified_entailment; simpl.
    split; intros.
    - pose (q1 := {|
        conf_state := e.(e_concl).(cr_st).(cs_st1).(st_state);
        conf_store := store1;
        conf_buf_sane := H0;
        conf_buf := buf1;
      |}).
      pose (q2 := {|
        conf_state := e.(e_concl).(cr_st).(cs_st2).(st_state);
        conf_store := store2;
        conf_buf_sane := H1;
        conf_buf := buf2;
      |}).
      replace buf1 with (conf_buf q1) by reflexivity.
      replace buf2 with (conf_buf q2) by reflexivity.
      replace store1 with (conf_store q1) by reflexivity.
      replace store2 with (conf_store q2) by reflexivity.
      apply simplify_conf_rel_correct with (c1 := q1) (c2 := q2); subst q1 q2.
      + apply H; auto.
        eapply simplify_crel_correct; try split.
        * now unfold interp_state_template; simpl.
        * now unfold interp_state_template; simpl.
        * unfold conf_to_state_template; simpl.
          now (destruct (e.(e_concl).(cr_st).(cs_st1));
               destruct (e.(e_concl).(cr_st).(cs_st2))).
        * apply H3.
      + now unfold interp_conf_state, interp_state_template; simpl.
    - apply simplify_conf_rel_correct; intros.
      destruct H1 as [[? ?] [? ?]].
      rewrite H2, H4 in H.
      apply H; auto.
      * unfold state_template_sane.
        rewrite H2, H1.
        apply q1.
      * unfold state_template_sane.
        rewrite H3, H4.
        apply q2.
      * clear H.
        induction (e_prem e).
        + cbn in H0.
          unfold conf_to_state_template in H0.
          rewrite <- H1, <- H2, <- H3, <- H4 in H0.
          destruct (cs_st1 (cr_st (e_concl e))).
          destruct (cs_st2 (cr_st (e_concl e))).
          now simpl in *.
        + rewrite interp_crel_cons in H0.
          apply IHc.
          intuition.
      * eapply simplify_crel_correct; auto.
        + now unfold interp_conf_state, interp_state_template.
        + exact H0.
  Qed.

  Lemma simplify_entailment_correct' (e: entailment):
    forall i: Relations.rel state_template,
      interp_entailment'
        (fun c1 c2 => i (conf_to_state_template c1)
                        (conf_to_state_template c2)) e <->
      interp_simplified_entailment' i (simplify_entailment e)
  .
  Proof.
    intros; split.
    - unfold interp_entailment',
           simplify_entailment,
           interp_simplified_entailment'; simpl; intros.
      pose (q1 := {|
        conf_state := e.(e_concl).(cr_st).(cs_st1).(st_state);
        conf_store := store1;
        conf_buf_sane := H0;
        conf_buf := buf1;
      |}).
      pose (q2 := {|
        conf_state := e.(e_concl).(cr_st).(cs_st2).(st_state);
        conf_store := store2;
        conf_buf_sane := H1;
        conf_buf := buf2;
      |}).
      replace buf1 with (conf_buf q1) in * by reflexivity.
      replace buf2 with (conf_buf q2) in * by reflexivity.
      replace store1 with (conf_store q1) in * by reflexivity.
      replace store2 with (conf_store q2) in * by reflexivity.
      pose proof (simplify_crel_correct i e.(e_prem)).
      specialize (H4 e.(e_concl).(cr_st) q1 q2).
      apply H4; try easy.
      apply H; try easy.
      subst q1 q2.
      now destruct e, e_concl0, cr_st0, cs_st3, cs_st4; simpl in *.
    - intros.
      unfold interp_simplified_entailment' in H.
      unfold interp_entailment'; intros.
      rewrite simplify_conf_rel_correct' in H1.
      rewrite simplify_crel_correct; intuition.
      replace (simplify_crel (e_prem e) (cr_st (e_concl e))) with (se_prems (simplify_entailment e)) by reflexivity.
      unfold interp_conf_state, interp_state_template in H2.
      destruct H2 as [[? ?] [? ?]].
      destruct q1, q2; simpl in *.
      unfold conf_to_state_template in *; simpl in *.
      rewrite H2, H5 in H.
      apply H.
      + unfold state_template_sane; congruence.
      + unfold state_template_sane; congruence.
      + destruct e, e_concl, cr_st, cs_st1, cs_st2; simpl in *.
        congruence.
      + apply H3.
  Qed.
End ConfRel.
Arguments interp_conf_rel {_} {_} {_} {_} {_} {_} a phi.
Arguments interp_crel {_} {_} {_} {_} {_} {_} a i rel.
Arguments interp_entailment {_ _ _ _ _ _} a i e.
