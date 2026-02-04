From Stdlib Require Import Strings.String.
From Stdlib Require Import String Ascii.
From Stdlib Require Arith.
From stdpp Require Import base.
From stdpp Require Import fin_maps.
From stdpp Require Import gmap.
From stdpp Require Import base gmultiset.
From Stdlib Require Classical.
From Stdlib Require Import ZArith.
From stdpp.bitvector Require Import definitions tactics.
From Stdlib Require Import Sorting.Sorted.
From Stdlib Require Import Reals.Rbasic_fun.
From Stdlib Require Import Reals.Abstract.ConstructiveAbs.
From Stdlib Require Import Reals.Rdefinitions.
From stdpp Require Import list_relations.
From stdpp Require Import list_numbers.
From stdpp Require Import functions.
From Stdlib Require Import ClassicalEpsilon.
From stdpp Require Import base decidable.
From Stdlib Require Import ZArith.Zeuclid.
From Stdlib Require Import ZArith.Znumtheory.
From stdpp Require Import propset.
From Stdlib Require Import Reals.
Require Import Why3.Base.
Open Scope Z_scope.
Inductive split (α : Type) :=
  | split'mk : list α -> option α -> list α -> split α.
Axiom split_inhabited : forall  {α : Type} `{Inhabited α}, Inhabited (split α).
Global Existing Instance split_inhabited.
Arguments split'mk {α}.
Definition left1 {α : Type} (x : split α) := match x with |  split'mk a _ _ => a end.
Definition middle {α : Type} (x : split α) := match x with |  split'mk _ a _ => a end.
Definition right1 {α : Type} (x : split α) := match x with |  split'mk _ _ a => a end.
Inductive part_base (α : Type) :=
  | Left : α -> part_base α
  | Right : α -> part_base α
  | Here : part_base α.
Axiom part_base_inhabited : forall  {α : Type} `{Inhabited α}, Inhabited (part_base α).
Global Existing Instance part_base_inhabited.
Arguments Left {α}.
Arguments Right {α}.
Arguments Here {α}.
Definition option_to_seq {α : Type} `{Inhabited α} (o1 : option α) : list α := match o1 with | Some x => ([x]:list α) | None => ([] : list α) end.
Definition rebuild {α : Type} `{Inhabited α} (p : split α) : list α := (left1 p ++ option_to_seq (middle p)) ++ right1 p.
Definition left_extend {α : Type} `{Inhabited α} (l : list α) (d : α) (e : split α) : split α := split'mk (l ++ cons d (left1 e)) (middle e) (right1 e).
Definition right_extend {α : Type} `{Inhabited α} (e : split α) (d : α) (r : list α) : split α := split'mk (left1 e) (middle e) (right1 e ++ cons d r).
