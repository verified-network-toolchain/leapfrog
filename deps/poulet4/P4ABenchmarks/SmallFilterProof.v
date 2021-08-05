Require Import Poulet4.P4automata.Examples.ProofHeader.
Require Import Poulet4.P4automata.Examples.SmallFilter.
From Hammer Require Import Tactics.


Notation H := (IncrementalBits.header + BigBits.header).
Notation A := IncrementalSeparate.aut.
Notation conf := (P4automaton.configuration (P4A.interp A)).
Lemma prebisim_incremental_sep:
  pre_bisimulation IncrementalSeparate.aut
                   (WPSymLeap.wp (H:=IncrementalSeparate.header))
                   (reachable _ _ _ IncrementalSeparate.aut 10 IncrementalBits.Start BigBits.Parse)
                   nil
                   (mk_init 10 IncrementalSeparate.aut IncrementalBits.Start BigBits.Parse)
                   (inl (inl IncrementalBits.Start), [], [])
                   (inl (inr BigBits.Parse), [], []).
Proof.
  set (r := (mk_init 10 IncrementalSeparate.aut IncrementalBits.Start BigBits.Parse)).
  cbv in r.
  subst r.
  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert
      (H :
         ~
           (forall q1 q2 : P4automaton.configuration (P4A.interp a),
               interp_crel i R q1 q2 -> interp_conf_rel C q1 q2))
  end.
  
  set (a:=IncrementalSeparate.aut).
  set (i:=(reachable IncrementalBits.state BigBits.state
        (Sum.H IncrementalBits.header BigBits.header) A 10 IncrementalBits.Start
        BigBits.Parse)) in *.
  rewrite (filter_entails (a:=a)) by typeclasses eauto.
  simpl.
  rewrite (no_state) by typeclasses eauto.
  repeat
    unfold interp_conf_rel, interp_conf_state, interp_state_template, interp_store_rel
     || cbn; eapply forall_exists; repeat (setoid_rewrite  <- split_univ; cbn).
  repeat (setoid_rewrite  <- split_ex; cbn).
  unfold not.
  eexists.
  eexists.
  exact tt.
  intros.
  eapply H.
  exact tt.
  cbv.

  break_store.
  sauto.
  solve [ sauto | unfold not; now break_store ].


  ; pose (t := wp a C);
    eapply PreBisimulationExtend with (H0 := right H) (W := t);
      [ tauto | reflexivity |  ]; compute in t; simpl (_ ++ _); 
        unfold t; clear t; clear H
  end.
  
         | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
           skip_bisim a wp i R C;
             idtac "Entailment holds:";
             let g := constr:(forall q1 q2 : P4automaton.configuration (P4A.interp a),
                          interp_crel i R q1 q2 -> interp_conf_rel C q1 q2) in
             idtac g
         | |- pre_bisimulation _ _ _ _ [] _ _ => apply PreBisimulationClose
         end.
  (*time (repeat (solve_bisim)).*)
  repeat (unfold interp_conf_rel, interp_conf_state, interp_state_template || cbn).
  intuition eauto;
  firstorder (try congruence);
  sauto limit:5000.

  Unshelve.
  all: (exact nil).
  
Time Qed.

Ltac break_store2 h0 h1 := 
  repeat match goal with
  | |- exists (x: P4A.store ?H), @?P x =>
    cut (exists y0 y1,
                P ([(h0, P4A.VBits y0);
                    (h1, P4A.VBits y1)]));
    [ intros [x0 [x1 ?]];
      exists ([(h0, P4A.VBits x0);
          (h1, P4A.VBits x1)]);
      eauto
      | trivial
    ];
    repeat eexists
  | |- (forall (x: P4A.store ?H), _) -> False =>
      intros
  | H: forall (x: P4A.store ?H), @?P x |- _ =>
      assert (forall y0 y1,
                  P ([(h0, P4A.VBits y0);
                      (h1, P4A.VBits y1)])); [
      cbn; sauto | 
      sauto
    ]
  end.

Ltac break_store4 h0 h1 h2 h3 := 
  repeat match goal with
  | |- exists (x: P4A.store ?H), @?P x =>
    cut (exists y0 y1 y2 y3,
                P ([(h0, P4A.VBits y0);
                    (h1, P4A.VBits y1);
                    (h2, P4A.VBits y2);
                    (h3, P4A.VBits y3)]));
    [ intros [x0 [x1 [x2 [x3 ?]]]];
      exists ([(h0, P4A.VBits x0);
          (h1, P4A.VBits x1);
          (h2, P4A.VBits x2);
          (h3, P4A.VBits x3)]);
      eauto
      | trivial
    ];
    repeat eexists
  | |- (forall (x: P4A.store ?H), _) -> False =>
      intros
  | H: forall (x: P4A.store ?H), @?P x |- _ =>
      assert (forall y0 y1 y2 y3,
                  P ([(h0, P4A.VBits y0);
                      (h1, P4A.VBits y1);
                      (h2, P4A.VBits y2);
                      (h3, P4A.VBits y3)])); [
      cbn; sauto | 
      match goal with |- ?H => idtac H end
    ]
  end.

Ltac break_store :=
  match goal with
  | |- context[ P4A.store ?H ] =>
    let hs := fresh "hdrs" in
    pose (hs := FinType.enum H);
    cbv in hs;
    match find hs with
    | [?h0; ?h1] => break_store2 h0 h1
    | [?h0; ?h1; ?h2; ?h3] => break_store4 h0 h1 h2 h3
    | _ => idtac hs
    end
  end.


Lemma intermediate_example:
  ~ (forall q1 q2 : conf,
 interp_crel
   (separated IncrementalBits.state BigBits.state
      (Sum.H IncrementalBits.header BigBits.header) A)
   [(BCSnoc BCEmp 1), ⟨ inl (inl IncrementalBits.Start), 0 ⟩ ⟨ 
    inl (inr BigBits.Parse), 1
    ⟩ ⊢ (BREq (BEHdr (BCSnoc BCEmp 1) Left (Syntax.HRVar (inl IncrementalBits.Pref)))
           (BELit (IncrementalBits.header + BigBits.header) (BCSnoc BCEmp 1) [true])
         ⇒ (BREq (BEHdr (BCSnoc BCEmp 1) Right (Syntax.HRVar (inr BigBits.Pref)))
              (BELit (IncrementalBits.header + BigBits.header) (BCSnoc BCEmp 1) [true])
            ⇒ bfalse));
   BCEmp, ⟨ inl (inl IncrementalBits.Finish), 0 ⟩ ⟨ inr true, 0 ⟩ ⊢ bfalse] q1 q2 ->
 interp_conf_rel (BCEmp, ⟨ inr true, 0 ⟩ ⟨ inl (inr BigBits.Parse), 1 ⟩ ⊢ bfalse) q1 q2).
Proof.
  rewrite (no_state _).
  repeat (unfold interp_conf_rel, interp_conf_state, interp_state_template, interp_store_rel || cbn).
  eapply forall_exists.
  repeat (setoid_rewrite <- split_univ; cbn).
  repeat (setoid_rewrite <- split_ex; cbn).
  unfold not.
  Print break_store.
  break_store.

  intros [[st1 store1] buf1] [[st2 store2] buf2].
  unfold interp_crel, interp_conf_rel, interp_conf_rel, interp_conf_state, interp_state_template; cbn.
  simpl;
  rewrite (no_state i) by (typeclasses eauto);
  repeat (unfold interp_conf_rel, interp_conf_state, interp_state_template, interp_store_rel || cbn);
  eapply forall_exists;
  repeat (setoid_rewrite <- split_univ; cbn);
  repeat (setoid_rewrite <- split_ex; cbn);
  (solve [sauto | unfold not; now break_store]).

  intros.
  intuition.
  break_store.
  break_store2
  break_store4 BigBits.Pref BigBits.Suf IncrementalBits.Pref IncrementalBits.Suf.
  cbv.
