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
Axiom model : Type -> Type -> Type.
Axiom model_inhabited : forall  {ty'key : Type} `{Inhabited ty'key} {ty'value : Type} `{Inhabited ty'value}, Inhabited (model ty'key ty'value).
Global Existing Instance model_inhabited.
Axiom t : Type -> Type -> Type.
Axiom t_inhabited : forall  {ty'key : Type} `{Inhabited ty'key} {ty'value : Type} `{Inhabited ty'value}, Inhabited (t ty'key ty'value).
Global Existing Instance t_inhabited.
Axiom model1 : forall {ty'value : Type} `{Inhabited ty'value} {ty'key : Type} `{Inhabited ty'key}, t ty'key ty'value -> ty'key -> option ty'value.
Definition get {ty'value : Type} {ty'key : Type} `{Inhabited ty'value} `{Inhabited ty'key} (d : t ty'key ty'value) (k : ty'key) : option ty'value := model1 d k.
