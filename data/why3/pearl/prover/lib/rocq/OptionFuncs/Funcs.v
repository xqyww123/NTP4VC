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
Open Scope Z_scope.
Axiom some : forall {α : Type} `{Inhabited α}, α -> option α.
Axiom some_def : forall  {α : Type} `{Inhabited α} (x : α), some x = Some x.
Axiom ocase : forall {α : Type} `{Inhabited α} {β : Type} `{Inhabited β}, (α -> β) -> β -> option α -> β.
Axiom ocase_def : forall  {α : Type} {β : Type} `{Inhabited α} `{Inhabited β} (f : α -> β) (d : β) (x : option α), ocase f d x = (match x with | None => d | Some x1 => f x1 end).
Definition omap {α : Type} {β : Type} `{Inhabited α} `{Inhabited β} (f : α -> β) (x : option α) : option β := match x with | None => (None : option β) | Some x1 => Some (f x1) end.
Definition olift {α : Type} {β : Type} `{Inhabited α} `{Inhabited β} (f : α -> β) : option α -> option β := ocase (compose some f) (None : option β).
