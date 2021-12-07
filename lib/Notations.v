Require Import Leapfrog.Syntax.

Declare Scope p4a_scope.
Delimit Scope p4a_scope with p4a.
Declare Scope p4a_cases_scope.
Delimit Scope p4a_cases_scope with p4ac.
Declare Scope p4a_bits_scope.
Delimit Scope p4a_bits_scope with p4abits.

Notation "e1 ;; e2" := (OpSeq e1%p4a e2%p4a)%p4a
  (at level 100, right associativity) : p4a_scope.

Notation "v <- e" := (OpAsgn v e%p4a)%p4a
  (at level 100): p4a_scope.

Notation "extract( hdr )" := (OpExtract _ hdr)%p4a (at level 60) : p4a_scope.

Notation " e [ hi -- lo ]" := (ESlice _ e%p4a hi lo)%p4a (at level 10) : p4a_scope.

Notation "(| e |)" := (CExpr e%p4a) : p4a_cases_scope.

Notation "(| x , .. , y , z |)" :=
    (CPair (CExpr x%p4a) .. (CPair (CExpr y%p4a) (CExpr z%p4a)) .. ) : p4a_cases_scope.

Notation "1" := (true) : p4a_bits_scope.
Notation "0" := (false) : p4a_bits_scope.

Notation "#b | x | .. | z" :=
  (let bs := (cons x%p4abits .. (cons z%p4abits nil) ..) in
    VBits (length bs) (Ntuple.l2t bs)
  ) (at level 60) : p4a_scope.

Notation "'transition' 'select' e {{ c1 ;;; c2 ;;; .. ;;; cn ;;; default }}" := (
    TSel e%p4ac (c1%p4a :: c2%p4a :: .. (cn%p4a :: nil) ..) default%p4a
    )%p4a
  (at level 60) : p4a_scope.

Notation "'transition' 'select' e {{ c ;;; default }}" := (TSel e%p4ac (c%p4a :: nil) default%p4a )%p4a
  (at level 60) : p4a_scope.

Notation "'transition' default" := (TGoto _ default%p4a)%p4a (at level 60): p4a_scope.

(* Notation "'accept'" := (inr true) : p4a_scope. *)
(* Notation "'reject'" := (inr false) : p4a_scope. *)
Definition accept {A} := @inr A _ true.
Definition reject {A} := @inr A _ false.

Notation "*" := (PAny _) : p4a_scope.
Notation "'exact' e" := (PExact e) (at level 60): p4a_scope.

Notation "'hexact' n" := (PExact (VBits _ (Ntuple.nat2t _ n))) (at level 60): p4a_scope.

Notation "[| x |] ==> target " := ({| sc_pat := x%p4a ; sc_st := target%p4a |}) (at level 60): p4a_scope.

Notation "[| x , .. , y , z |] ==> target" :=
  ({| sc_pat := (PPair x%p4a .. (PPair y%p4a z%p4a) .. ) ; sc_st := target%p4a |}) (at level 60): p4a_scope.
