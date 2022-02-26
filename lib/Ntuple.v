Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.JMeq.
Require Import Coq.Init.Peano.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.EquivDec.
From Equations Require Import Equations.

Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.


Import ListNotations.

Set Universe Polymorphism.

Inductive len_pf {A}: list A -> nat -> Prop :=
  | len_nil : len_pf nil 0
  | len_suc : 
    forall xs n, 
    len_pf xs n -> 
    forall v, len_pf (v :: xs) (S n).

Derive Signature for len_pf.

Lemma len_pf_conv : 
  forall A (xs: list A) n, 
    len_pf xs n -> length xs = n.
Proof.
  intros.
  induction H.
  - exact eq_refl.
  - simpl.
    erewrite IHlen_pf.
    exact eq_refl.
Qed.

Lemma len_pf_rev : 
  forall A (xs: list A) n,
    length xs = n -> 
    len_pf xs n.
Proof.
  intros ? ?.
  induction xs.
  - intros; simpl.
    inversion H.
    simpl.
    econstructor.
  - intros.
    simpl in *.
    destruct n; [exfalso; inversion H|].
    econstructor.
    eapply IHxs.
    inversion H.
    exact eq_refl.
Qed.

Require Import Coq.Program.Equality.
Lemma lenpf_uniq A n (xs: list A): 
  forall (x y: len_pf xs n),
    x = y.
Proof.
  revert xs.
  induction n.
  - intros.
    dependent destruction x;
    dependent destruction y;
    exact eq_refl.
  - intros.
    dependent destruction x.
    dependent destruction y.
    pose proof (IHn xs x y).
    subst.
    exact eq_refl.
Defined.

Ltac simpl_lenpf := 
  match goal with 
  | |- exist _ _ ?x = exist _ _ ?y => 
    let H := fresh "H" in 
    assert (H: x = y) by eapply lenpf_uniq;
    erewrite H;
    clear H
  | |- exist _ _ ?x ~= exist _ _ ?y => 
    let H := fresh "H" in 
    assert (H: x = y) by eapply lenpf_uniq;
    erewrite H;
    clear H
  end.

Equations len_pf_prev {A} {n: nat} {xs: list A} (pf: len_pf xs (S n)) : len_pf (tl xs) n :=
  len_pf_prev (len_suc _ _ pf _) := pf.

Equations len_pf_concat {A} {n m: nat} {xs ys: list A} (l: len_pf xs n) (r: len_pf ys m) : len_pf (xs ++ ys) (n + m) :=
  len_pf_concat len_nil r := r;
  len_pf_concat (len_suc _ _ l _) r := len_suc _ _ (len_pf_concat l r) _.

Definition n_tuple A (n: N): Type :=
  {xs : list A | len_pf xs (N.to_nat n)}.

Definition n_tuple_emp {A} : n_tuple A 0 := exist _ nil len_nil.

Program Definition n_tuple_prev {A n} (xs: n_tuple A (N.succ n)) : n_tuple A n :=
  match xs with 
  | _ :: xs => xs
  | nil => _
  end.
Next Obligation.
  destruct xs0.
  simpl in *.
  destruct x; [exfalso; congruence|].
  inversion Heq_xs.
  assert (tl (a :: x) = x) by exact eq_refl.
  erewrite <- H.
  eapply len_pf_prev.
  erewrite N2Nat.inj_succ in l.
  exact l.
Defined.
Next Obligation.
  destruct xs.
  simpl in *.
  subst.
  erewrite N2Nat.inj_succ in l.
  pose proof (len_pf_conv _ _ _ l).
  inversion H.
Defined.

Lemma n_tuple_emp_uniq: 
  forall A (x: n_tuple A 0), x = n_tuple_emp.
Proof.
  intros.
  unfold n_tuple_emp.
  destruct x.
  dependent destruction l.
  exact eq_refl.
Qed.


Program Definition n_tuple_snoc {A n} (xs: n_tuple A n) (x: A) : n_tuple A (n + 1) := xs ++ [x].
Next Obligation.
  eapply len_pf_rev.
  destruct xs.
  pose proof len_pf_conv _ _ _ l.
  simpl.
  clear l.
  destruct n.
  - simpl.
    inversion H.
    destruct x0; [|exfalso; inversion H1].
    exact eq_refl.
  - erewrite app_length.
    simpl in *.
    Lia.lia.
Defined.

Program Definition n_tuple_cons {A n} (xs: n_tuple A n) (x: A) : n_tuple A (n + 1) := x :: xs.
Next Obligation.
  destruct xs.
  simpl.
  eapply len_pf_rev.
  pose proof len_pf_conv _ _ _ l.
  simpl.
  Lia.lia.
Defined.

Program Definition n_tuple_cons_succ {A n} (xs: n_tuple A n) (x: A) : n_tuple A (N.succ n) := n_tuple_cons xs x.
Next Obligation.
  destruct xs.
  simpl.
  erewrite N2Nat.inj_succ.
  econstructor.
  auto.
Defined.

Definition t2l {A: Type} {n: N} (x: n_tuple A n) : list A := proj1_sig x.

Lemma t2l_len {A} n: forall (x: n_tuple A n), length (t2l x) = N.to_nat n.
Proof.
  intros.
  destruct x.
  pose proof len_pf_conv _ _ _ l.
  simpl in *.
  auto.
Qed.

Definition rewrite_size {A n m} (pf: m = n) (l: n_tuple A n) : n_tuple A m :=
  eq_rect_r (fun m' => n_tuple A m') l pf.

Program Fixpoint l2t {A: Type} (l: list A) : n_tuple A (N.of_nat (length l)) :=
  match l as l' return n_tuple A (N.of_nat (length l')) with
  | nil => nil
  | a::l => (l2t l) ++ [a]
  end.
Next Obligation.
  econstructor.
Defined.
Next Obligation.
  eapply len_pf_rev.
  erewrite app_length.
  pose proof len_pf_conv _ _ _ l1.
  simpl in *.
  Lia.lia.
Defined.

Program Fixpoint nat2t (n: nat) (v: nat) : n_tuple bool (N.of_nat n) :=
  match n as n' return n_tuple bool (N.of_nat n') with
  | 0 => nil
  | S n =>
    n_tuple_snoc (nat2t n (Nat.div2 v)) (Nat.eqb (Nat.modulo v 2) 1)
  end.
Next Obligation.
  econstructor.
Defined.
Next Obligation.
  eapply len_pf_rev.
  erewrite app_length.
  simpl.
  pose proof len_pf_conv _ _ _ l.
  Lia.lia.
Defined.



Program Fixpoint n_tuple_repeat {A: Type} (n: nat) (a: A) : n_tuple A (N.of_nat n) :=
  match n with
  | 0 => nil
  | S n => n_tuple_snoc (n_tuple_repeat n a) a
  end.
Next Obligation.
  econstructor.
Defined.
Next Obligation.
  eapply len_pf_rev.
  pose proof len_pf_conv _ _ _ l.
  erewrite app_length.
  simpl.
  Lia.lia.
Defined.

Equations n_tuple_concat {A n m} (xs: n_tuple A n) (ys: n_tuple A m) : n_tuple A (n + m) := 
  n_tuple_concat (exist _ xs xp) (exist _ ys yp) := exist _ (xs ++ ys) _.
Next Obligation.
  erewrite N2Nat.inj_add.
  eapply len_pf_concat; eauto.
Defined.

Lemma n_tuple_concat_emp_l:
  forall A n (xs: n_tuple A n), 
    n_tuple_concat n_tuple_emp xs = xs.
Proof.
  intros.
  destruct xs.
  unfold n_tuple_emp.
  autorewrite with n_tuple_concat.
  simpl.
  simpl_lenpf.
  auto.
Qed.

Lemma add_0_r: 
  forall (n: N), (n + 0 = n)%N.
Proof.
  intros; Lia.lia.
Qed.

  

(* Lemma n_tuple_concat_emp_r:
  forall A n (xs: n_tuple A n), 
    eq_rect (n + 0)%N (fun n0 : N => n_tuple A n0)  (n_tuple_concat xs n_tuple_emp) n (add_0_r n) =
    xs.
Proof.
  intros.
  unfold n_tuple_emp.
  simpl.
  unfold eq_rect.
  simpl.
Admitted. *)

Global Instance n_tuple_eq_dec
         {A: Type}
         `{A_eq_dec: EquivDec.EqDec A eq}
         (n: N) : EquivDec.EqDec (n_tuple A n) eq.
Proof.
  unfold EquivDec.EqDec; intros.
  destruct x as [x xe].
  destruct y as [y ye].
  
  destruct (list_eq_dec A_eq_dec x y); subst.
  
  - left.
    unfold "===".
    simpl_lenpf.
    exact eq_refl.
  - right.
    unfold "=/=".
    intros.
    eapply n0.
    inversion H.
    trivial.
Defined.

Lemma min_0_r : forall n, Nat.min n 0 = 0.
Proof.
  intros.
  eapply min_r; eapply le_0_n.
Qed.
Lemma min_0_l : forall n, Nat.min 0 n = 0.
Proof.
  intros.
  eapply min_l; eapply le_0_n.
Qed.

Program Definition n_tuple_take_n {A m} (n: N) (xs: n_tuple A m) : n_tuple A (N.min n m) :=
  rewrite_size _ (l2t (firstn (N.to_nat n) (t2l xs))).
Next Obligation.
  rewrite firstn_length.
  rewrite t2l_len.
  erewrite Nat2N.inj_min.
  repeat erewrite N2Nat.id.
  exact eq_refl.
Defined.

Program Definition n_tuple_skip_n {A m} (n: N) (xs: n_tuple A m) : n_tuple A (m - n) :=
  rewrite_size _ (l2t (skipn (N.to_nat n) (t2l xs))).
Next Obligation.
  rewrite skipn_length.
  rewrite t2l_len.
  erewrite Nat2N.inj_sub.
  repeat erewrite N2Nat.id.
  exact eq_refl.
Defined.

Program Definition n_tuple_slice {A n} (hi lo: N) (xs: n_tuple A n) : n_tuple A (N.min (1 + hi) n - lo) :=
  n_tuple_skip_n lo (n_tuple_take_n (1 + hi) xs).

Lemma rewrite_size_eq:
  forall n (x: n_tuple bool n) (pf: n = n),
    Ntuple.rewrite_size pf x = x.
Proof.
  unfold Ntuple.rewrite_size, eq_rect_r.
  intros.
  rewrite <- eq_rect_eq_dec; eauto.
  apply N.eq_dec.
Qed.

Lemma rewrite_size_jmeq:
  forall A n m (x: Ntuple.n_tuple A m) (pf: n = m),
    JMeq (Ntuple.rewrite_size pf x) x.
Proof.
  unfold Ntuple.rewrite_size, eq_rect_r.
  intros.
  destruct pf.
  reflexivity.
Qed.

Lemma concat_emp:
  forall A n (t: n_tuple A n),
    (n_tuple_concat n_tuple_emp t) ~= t.
Proof.
  intros.
  erewrite n_tuple_concat_emp_l.
  reflexivity.
Qed.
(* 
Lemma concat'_cons:
  forall A n m (xs: n_tuple A n) (ys: n_tuple A m) a,
    JMeq (n_tuple_cons (n_tuple_concat' xs ys) a)
         (n_tuple_concat' (n_tuple_cons xs a) ys).
Proof.
  intros.
  induction m; simpl; destruct ys.
  - reflexivity.
  - assert (JMeq (n_tuple_cons (n_tuple_concat' xs n0) a, a0)
                 (n_tuple_concat' (n_tuple_cons xs a) n0, a0))
      by (rewrite IHm; reflexivity).
    eauto using JMeq_trans.
Qed.

Lemma concat_cons:
  forall bool n m (xs: n_tuple bool n) (ys: n_tuple bool m) a,
    JMeq (n_tuple_cons (n_tuple_concat xs ys) a)
         (n_tuple_concat (n_tuple_cons xs a) ys).
Proof.
  intros.
  unfold n_tuple_concat.
  generalize (n_tuple_concat_obligation_1 bool (1 + n) m).
  generalize (n_tuple_concat_obligation_1 bool n m).
  intros e e0.
  rewrite e, e0.
  replace (rewrite_size eq_refl _) with (n_tuple_concat' xs ys).
  replace (rewrite_size eq_refl _) with (n_tuple_concat' (n_tuple_cons xs a) ys).
  - now rewrite concat'_cons.
  - apply JMeq_eq.
    now rewrite rewrite_size_jmeq.
  - apply JMeq_eq.
    now rewrite rewrite_size_jmeq.
Qed. *)

Section ConvProofs.
  Set Universe Polymorphism.
  Variable (A: Type).

  Lemma l2t_app:
    forall (xs ys: list A),
      (l2t (xs ++ ys)) ~= (n_tuple_concat (l2t xs) (l2t ys)).
  Proof.
    induction xs; intros.
    - apply JMeq_sym.
      apply concat_emp.
    - pose proof (IHxs ys).
      simpl l2t.
      set (t := l2t ys) in *.
      destruct t.
      autorewrite with n_tuple_concat in *.
  Admitted.
     
      (* assert (JMeq (n_tuple_cons (l2t (xs ++ ys)) a)
                   (n_tuple_cons (n_tuple_concat (l2t xs) (l2t ys)) a)).
      {
        generalize dependent (l2t (xs ++ ys)).
        rewrite app_length.
        erewrite Nat2N.inj_add.
        intros.
        erewrite H.
        reflexivity.
      }
      eapply JMeq_trans.
      apply concat_cons.
  Qed. *)
 
  Lemma l2t_t2l:
    forall n (t: n_tuple A n),
      (l2t (t2l t)) ~= t.
  Proof.
  Admitted.
(*
    induction n; intros; destruct t.
    - reflexivity.
    - cbn.
      pose proof (l2t_app (t2l n0) [a]).
      eapply JMeq_trans.
      eapply H.
      cbn.
      assert (JMeq
                (n_tuple_concat (l2t (t2l n0)) ((tt, a): n_tuple _ 1))
                (l2t (t2l n0), a)).
      {
        generalize (l2t (t2l n0)).
        generalize (length (t2l n0)).
        unfold n_tuple_concat.
        intro n1.
        generalize (n_tuple_concat_obligation_1 A n1 1).
        intros.
        cbn in *.
        apply rewrite_size_jmeq.
      }
      eapply JMeq_trans.
      eapply H0.
      eapply JMeq_sym.
      specialize (IHn n0).
      revert IHn.
      generalize dependent (l2t (t2l n0)).
      rewrite t2l_len.
      intros.
      rewrite IHn.
      reflexivity.
  Qed.
*)

  Lemma t2l_cons:
    forall n (t: n_tuple A n) x,
      t2l (n_tuple_cons t x) = x :: t2l t.
  Proof.
  Admitted.
    (* induction n.
    - reflexivity.
    - intros.
      destruct t.
      simpl.
      replace (x :: t2l n0 ++ [a])
        with ((x :: t2l n0) ++ [a])
        by eauto with datatypes.
      rewrite <- IHn.
      remember (n_tuple_cons n0 x) as g.
      simpl in *.
      now destruct g.
  Qed. *)
(*
  Lemma t2l_l2t:
    forall (l: list A),
      Ntuple.t2l (l2t l) = l.
  Proof.
    induction l.
    - reflexivity.
    - simpl (l2t _ ).
      replace (a :: l) with (a :: t2l (l2t l)) by (rewrite IHl; auto).
      apply t2l_cons.
  Qed.

End ConvProofs.

Lemma t2l_n_tuple_take_n:
  forall n m (t: n_tuple bool n),
    t2l (n_tuple_take_n m t) = firstn m (t2l t).
Proof.
  intros.
  unfold n_tuple_take_n.
  generalize (Ntuple.n_tuple_take_n_obligation_1 bool n m t).
  generalize (Nat.min m n).
  intros.
  subst.
  rewrite rewrite_size_eq.
  rewrite (t2l_l2t bool).
  reflexivity.
Qed.

Lemma t2l_n_tuple_skip_n:
  forall n m (t: n_tuple bool n),
    t2l (n_tuple_skip_n m t) = skipn m (t2l t).
Proof.
  intros.
  unfold n_tuple_skip_n.
  generalize (Ntuple.n_tuple_skip_n_obligation_1 bool n m t).
  generalize (n - m).
  intros.
  subst.
  rewrite rewrite_size_eq.
  rewrite t2l_l2t.
  reflexivity.
Qed. *)
End ConvProofs.