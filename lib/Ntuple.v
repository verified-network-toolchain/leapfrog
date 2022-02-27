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
Require Import Coq.PArith.BinPosDef.

Require Import Leapfrog.Classes.


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

Record n_tuple A (n: N) := mk_n_tup {
  elems : list A; 
  len: N
}.

Arguments elems {_ _} _.
Arguments len {_ _ } _.

Definition n_tup_wf {A n} (t: n_tuple A n) := len_pf t.(elems) (N.to_nat t.(len)) /\ n = t.(len).

Definition n_tuple_emp {A} : n_tuple A 0 := {| elems := nil; len := 0%N |}.

Definition n_tup_emp_wf : forall A, n_tup_wf (@n_tuple_emp A) := 
  fun _ => conj len_nil eq_refl.

Definition n_tuple_prev {A n} (xs: n_tuple A (N.succ n)) : n_tuple A n := {|
  elems := List.tl xs.(elems);
  len := N.pred xs.(len)
|}.

Lemma n_tuple_emp_uniq: 
  forall A (x: n_tuple A 0), 
    n_tup_wf x ->   
    x = n_tuple_emp.
Proof.
  intros.
  inversion H.
  destruct x.
  simpl in *.
  inversion H0; simpl in *; subst; unfold n_tuple_emp; trivial.
  inversion H2.
Qed.


Definition n_tuple_snoc {A n} (xs: n_tuple A n) (x: A) : n_tuple A (n + 1) := {|
  elems := xs.(elems) ++ [x];
  len := xs.(len) + 1
|}.

Definition n_tuple_cons {A n} (xs: n_tuple A n) (x: A) : n_tuple A (n + 1) := {|
  elems := x :: xs.(elems);
  len := xs.(len) + 1
|}.

Definition n_tuple_cons_succ {A n} (xs: n_tuple A n) (x: A) : n_tuple A (N.succ n) := {|
  elems := x :: xs.(elems);
  len := N.succ xs.(len)
|}.

Definition t2l {A: Type} {n: N} (x: n_tuple A n) : list A := x.(elems).

Lemma t2l_len {A} n: forall (x: n_tuple A n), n_tup_wf x -> length (t2l x) = N.to_nat n.
Admitted.
(* Proof.
  intros.
  destruct x.
  pose proof len_pf_conv _ _ _ l.
  simpl in *.
  auto.
Qed. *)

Definition rewrite_size {A n m} (pf: m = n) (l: n_tuple A n) : n_tuple A m := 
  eq_rect_r (fun m' => n_tuple A m') l pf.

Definition l2t {A: Type} (l: list A) : n_tuple A (N.of_nat (length l)) := {|
  elems := l;
  len := (N.of_nat (length l))
|}.

Fixpoint p2digs (p: positive) : list bool :=
  match p with 
  | xH => [true]
  | xO p' => false :: p2digs p'
  | xI p' => true :: p2digs p'
  end.

Definition n2digs (n: N) : list bool :=
  match n with 
  | 0%N => nil
  | N.pos p => p2digs p
  end. 

Fixpoint p2digs_sz (p: positive) : {r: (list bool * nat) & len_pf (fst r) (snd r)} :=
  match p with 
  | xH => existT _ ([true], 1) (len_suc _ _ len_nil _)
  | xO p' => 
    let (r, pf) := p2digs_sz p' in 
      existT _ (false :: fst r, S (snd r)) (len_suc _ _ pf _)
  | xI p' => 
    let (r, pf) := p2digs_sz p' in 
      existT _ (true :: fst r, S (snd r)) (len_suc _ _ pf _)
  end.

Fixpoint size_N (p: positive) : N := 
  match p with 
  | xH => 1%N
  | xI p'
  | xO p' => N.succ (size_N p')
  end.

Lemma p_digs_sz : 
  forall p r, 
    p2digs_sz p = r -> 
    N.of_nat (snd (projT1 r)) = size_N p. 
Proof.
  intros p.
  induction p; simpl; intros; (try now ( subst; exact eq_refl));
  destruct r;
  destruct x;
  simpl in *;
  pose proof (IHp (p2digs_sz p));
  erewrite <- H0; trivial;
  simpl;
  destruct (p2digs_sz p);
  simpl in *;
  clear H0;
  inversion H;
  subst;
  erewrite Nat2N.inj_succ;
  exact eq_refl.
Defined.

Definition p2nt (p: positive) : n_tuple bool (size_N p) := {|
  elems := p2digs p;
  len := size_N p
|}.

(* I think this is exactly log2 but not positive, it should be *)
Definition N_size_N (n: N) : N := 
  match n with 
  | 0%N => 0
  | N.pos p => size_N p
  end.

Definition n2t (n: N) : n_tuple bool (N_size_N n) :=
  match n with 
  | 0%N => n_tuple_emp
  | N.pos p => p2nt p
  end. 


Definition n_tuple_repeat {A: Type} (n: nat) (a: A) : n_tuple A (N.of_nat n) := {|
  elems := List.repeat a n; 
  len := N.of_nat n
|}.

Definition n_tuple_repeat_N {A} (n: N) (a: A) : n_tuple A n :=
  N.peano_rect _ n_tuple_emp (fun _ r => n_tuple_cons_succ r a) n.

Definition n_tuple_concat {A n m} (xs: n_tuple A n) (ys: n_tuple A m) : n_tuple A (n + m) := {|
  elems := xs.(elems) ++ ys.(elems);
  len := n + m
|}.

Definition minus_max m n := (m - n + n)%N.

Definition n_tuple_pad {A n m} (x: A) (xs: n_tuple A n) : n_tuple A (minus_max m n) :=
  n_tuple_concat (n_tuple_repeat_N (m - n) x) xs.
  
Lemma n_tuple_concat_emp_l:
  forall A n (xs: n_tuple A n), 
    n_tup_wf xs ->
    n_tuple_concat n_tuple_emp xs = xs.
Proof.
  intros.
  inversion H.
  subst.
  vm_compute.
  destruct xs.
  erewrite H1.
  exact eq_refl.
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

(* TODO: if this needs to be fast, we can replace with a custom version that avoids rewrites *)
Global Instance n_tuple_eq_dec
         {A: Type}
         `{A_eq_dec: EquivDec.EqDec A eq}
         (n: N) : EquivDec.EqDec (n_tuple A n) eq.
refine (
  fun x y => 
    match x, y with 
    | mk_n_tup _ _ xs x_len, mk_n_tup _ _ ys y_len => 
      match list_eq_dec A_eq_dec xs ys with 
      | left H_elems => 
        match N_eqdec x_len y_len with 
        | left H_len => left
          (eq_ind_r
            (fun xs0 : list A =>
              {| elems := xs0; len := x_len |} ===
              {| elems := ys; len := y_len |})
            (eq_ind_r
              (fun x_len0 : N =>
                {| elems := ys; len := x_len0 |} ===
                {| elems := ys; len := y_len |}) 
              eq_refl H_len) H_elems)
        | right H_len => right _
        end
      | right H_elems => right _
      end
    end
); congruence.
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

Definition n_tuple_take_n {A m} (n: N) (xs: n_tuple A m) : n_tuple A (N.min n m) := {|
  elems := firstn (N.to_nat n) (t2l xs);
  len := N.min n xs.(len)
|}.

Definition n_tuple_skip_n {A m} (n: N) (xs: n_tuple A m) : n_tuple A (m - n) := {|
  elems := skipn (N.to_nat n) (t2l xs);
  len := (m - n)
|}.

Definition n_tuple_slice {A n} (hi lo: N) (xs: n_tuple A n) : n_tuple A (N.min (1 + hi) n - lo) :=
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
    (Ntuple.rewrite_size pf x) ~= x.
Proof.
  unfold Ntuple.rewrite_size, eq_rect_r.
  intros.
  destruct pf.
  reflexivity.
Qed.

Lemma concat_emp:
  forall A n (t: n_tuple A n),
    n_tup_wf t -> 
    (n_tuple_concat n_tuple_emp t) ~= t.
Proof.
  intros.
  erewrite n_tuple_concat_emp_l;
  trivial.
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

Definition slice {A} (l: list A) (hi lo: N) :=
  List.skipn (N.to_nat lo) (List.firstn (1 + (N.to_nat hi)) l).

Lemma slice_len:
  forall A (hi lo: N) (l: list A),
    length (slice l hi lo) = N.to_nat (N.min (1 + hi) (N.of_nat (length l)) - lo)%N.
Proof.
  unfold slice.
  intros.
  rewrite List.skipn_length.
  rewrite List.firstn_length.
  erewrite N2Nat.inj_sub.
  erewrite N2Nat.inj_min.
  erewrite N2Nat.inj_add.
  erewrite Nat2N.id.
  trivial.
Qed.

Definition n_slice {A n} (l: n_tuple A n) (hi lo: N) : n_tuple A (N.min (1 + hi) n - lo)%N := {|
  elems := slice l.(elems) hi lo;
  len := (N.min (1 + hi) n - lo)%N
|}.

Section ConvProofs.
  Set Universe Polymorphism.
  Variable (A: Type).

  Lemma l2t_app:
    forall (xs ys: list A),
      (l2t (xs ++ ys)) ~= (n_tuple_concat (l2t xs) (l2t ys)).
  Proof.
    (* induction xs; intros.
    - apply JMeq_sym.
      apply concat_emp.
    - pose proof (IHxs ys).
      simpl l2t.
      set (t := l2t ys) in *.
      destruct t.
      autorewrite with n_tuple_concat in *. *)
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