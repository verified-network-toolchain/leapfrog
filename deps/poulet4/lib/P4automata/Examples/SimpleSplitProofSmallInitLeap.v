Require Import Poulet4.P4automata.Examples.ProofHeader.
Require Import Poulet4.P4automata.Examples.SimpleSplit.
Require Import SMTCoq.SMTCoq.
Require Import ZArith List Bool.


Definition possibly_unsound_init_rel
  : crel (Simple.state + Split.state) (Sum.H Simple.header Split.header)
  :=
    (mk_init 100 SimpleSplit.aut Simple.Start Split.StSplit1). 

(*
Ltac solve_bisim' :=
  match goal with
  | |- pre_bisimulation _ _ _ _ [] _ _ => apply PreBisimulationClose
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: {R ⊨ C} + {~(R ⊨ C)})
      by idtac;
    destruct H;
    [
        let t := fresh "tmp" in
        pose (t := wp a C); apply PreBisimulationExtend with (W := t);
         [ reflexivity |  ]; compute in t; unfold t; clear t;
         simpl (_ ++ _)
  end
*)


Notation i := (separated _ _ _ SimpleSplit.aut).
Notation "⟦ x ⟧" := (interp_crel i x).
Notation "⦇ x ⦈" := (interp_conf_rel (a:=SimpleSplit.aut) x).
Notation "R ⊨ q1 q2" := (⟦R⟧ q1 q2) (at level 40).
Notation "R ⊨ S" := (forall q1 q2, ⟦R⟧ q1 q2 -> ⦇S⦈ q1 q2) (at level 40).

Lemma forall_exists:
  forall {A B} (P: A -> B -> Prop),
  (exists x y, ~ P x y) ->
  ~ (forall x y, P x y).
Proof.
  firstorder.
Qed.

Lemma double_neg: 
  forall {A B} (P: A -> B -> Prop),
  (exists x y, P x y) ->
  (exists x y, ~ (P x y -> False)).
Proof.
  intros.
  destruct H as [x [y H]].
  exists x.
  exists y.
  intuition.
Qed.

(* Ltac break_products :=
  match goal with 
  | *)

Lemma prebisim_simple_split_sym_small_init_leap:
  pre_bisimulation SimpleSplit.aut
                   (WPSymLeap.wp (H:=SimpleSplit.header))
                   (separated _ _ _ SimpleSplit.aut)
                   nil
                   possibly_unsound_init_rel
                   (inl (inl Simple.Start), [], [])
                   (inl (inr Split.StSplit1), [], []).
Proof.
  set (r := possibly_unsound_init_rel).
  cbv in r.
  subst r.
  match goal with
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    assert (~(R ⊨ C))
  end.
  simpl.
  unfold interp_conf_rel.
  unfold P4automaton.configuration.
  simpl.
  unfold "⊨".
  unfold interp_conf_state, interp_state_template.
  simpl.
  unfold i.
  eapply forall_exists.
    
  (* a hand-simplified obligation that works with a weird eexists trick *)
  assert (exists
    (_ : 
                                               P4A.store
                                                 (Sum.H Simple.header
                                                 Split.header))
    (x : Sum.S Simple.state Split.state + bool) 
  (y0 : list bool) (y1 y2 y3 y4 y5 y6 y7 y8 y10 y11 : bool) 
  (x0 : Simple.state + Split.state + bool) (y9 : list bool) 
  (x1 : Simple.state) (x2 : Split.state),
    (x0 = inl (inl x1) \/ x0 = inr y10) /\ (x = inl (inr x2) \/ x = inr y11) ->
    (inl (inl Simple.Start) = x0 /\ y9 = [y1; y2; y3; y4; y5; y6; y7; y8]) /\
    inr true = x /\ (exists _ : unit, y0 = [])).
    eexists.
    Hammer.hammer. 
    Hammer.hammer.
  admit.
Admitted.
