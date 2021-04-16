Require Import Coq.Lists.List.
Require Import Typed.
Require Import Syntax.
Require Export Maps.
Import ListNotations.

Section SyntaxUtil.

Context {tags_t: Type}.
Notation Val := (@ValueBase tags_t).

Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).

Axiom dummy_ident : unit -> ident. (* make it lazy for extracted OCaml. *)
Axiom dummy_val : Val.

Definition get_type_name (typ : @P4Type tags_t) : ident :=
  match typ with
  | TypSpecializedType (TypTypeName (BareName type_name)) _ => type_name
  | TypTypeName (BareName type_name) => type_name
  | _ => dummy_ident tt
  end.

Definition get_param_name (param : @P4Parameter tags_t) : ident :=
  match param with
  | MkParameter _ _ _ _ name => name
  end.

Definition get_param_dir (param : @P4Parameter tags_t) : direction :=
  match param with
  | MkParameter _ dir _ _ _ => dir
  end.

Definition get_param_name_dir (param : @P4Parameter tags_t) : ident * direction :=
  match param with
  | MkParameter _ dir _ _ name => (name, dir)
  end.

Definition force {A} (default : A) (x : option A) : A :=
  match x with
  | Some x => x
  | None => default
  end.

Definition map_fst {A B C} (f : A -> B) (p : A * C) : B * C :=
  let (a, c) := p in (f a, c).

Definition map_snd {A B C} (f : A -> B) (p : C * A) : C * B :=
  let (c, a) := p in (c, f a).

End SyntaxUtil.
