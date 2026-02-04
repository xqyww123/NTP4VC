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
Require Import prover.Functions.Config.
Require Import prover.Functions.Func.
Require Import prover.Predicates.Pred.
Open Scope Z_scope.
Inductive timestamp (α : Type) :=
  | timestamp'mk : Z -> Z -> (Z -> list α) -> timestamp α.
Axiom timestamp_inhabited : forall  {α : Type} `{Inhabited α}, Inhabited (timestamp α).
Global Existing Instance timestamp_inhabited.
Arguments timestamp'mk {α}.
Definition time {α : Type} (x : timestamp α) := match x with |  timestamp'mk a _ _ => a end.
Definition size {α : Type} (x : timestamp α) := match x with |  timestamp'mk _ a _ => a end.
Definition table {α : Type} (x : timestamp α) := match x with |  timestamp'mk _ _ a => a end.
Inductive t (α : Type) :=
  | t'mk : list Z -> Z -> list (list α) -> (α -> bool) -> t α.
Axiom t_inhabited : forall  {α : Type} `{Inhabited α}, Inhabited (t α).
Global Existing Instance t_inhabited.
Arguments t'mk {α}.
Definition history {α : Type} (x : t α) := match x with |  t'mk a _ _ _ => a end.
Definition current_time {α : Type} (x : t α) := match x with |  t'mk _ a _ _ => a end.
Definition buffer {α : Type} (x : t α) := match x with |  t'mk _ _ a _ => a end.
Definition inv {α : Type} (x : t α) := match x with |  t'mk _ _ _ a => a end.
