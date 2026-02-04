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
Open Scope Z_scope.
Definition extensionalEqual {α : Type} {β : Type} `{Inhabited α} `{Inhabited β} (f : α -> β) (g : α -> β) := ∀(x : α), f x = g x.
Axiom functionExtensionality : forall  {α : Type} {β : Type} `{Inhabited α} `{Inhabited β} (f : α -> β) (g : α -> β) (fact0 : extensionalEqual f g), f = g.
Axiom update : forall {α : Type} `{Inhabited α} {β : Type} `{Inhabited β}, (α -> β) -> α -> β -> α -> β.
Axiom update_def : forall  {α : Type} {β : Type} `{Inhabited α} `{Inhabited β} (f : α -> β) (x : α) (y : β) (z : α), update f x y z = (if decide (x = z) then y else f z).
Axiom identity : forall {α : Type} `{Inhabited α}, α -> α.
Axiom identity_def : forall  {α : Type} `{Inhabited α} (x : α), identity x = x.
Axiom compose : forall {α : Type} `{Inhabited α} {β : Type} `{Inhabited β} {γ : Type} `{Inhabited γ}, (β -> γ) -> (α -> β) -> α -> γ.
Axiom compose_def : forall  {α : Type} {β : Type} {γ : Type} `{Inhabited α} `{Inhabited β} `{Inhabited γ} (g : β -> γ) (f : α -> β) (x : α), compose g f x = g (f x).
Axiom const : forall {α : Type} `{Inhabited α} {β : Type} `{Inhabited β}, β -> α -> β.
Axiom const_def : forall  {α : Type} {β : Type} `{Inhabited α} `{Inhabited β} (x : β) (z : α), (const : β -> α -> β) x z = x.
