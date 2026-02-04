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
Require Import prover.Nat.Nat.
Require Import prover.Functions.Config.
Require Import prover.Functions.Func.
Require Import prover.OptionFuncs.Funcs.
Require Import prover.Sum.Sum.
Require Import prover.Firstorder_symbol_spec.Spec.
Open Scope Z_scope.
Inductive fo_term_list (ty'b0 : Type) (ty'b3 : Type) :=
  | FONil : fo_term_list ty'b0 ty'b3
  | FOCons : fo_term ty'b0 ty'b3 -> fo_term_list ty'b0 ty'b3 -> fo_term_list ty'b0 ty'b3
with fo_term (ty'b0 : Type) (ty'b3 : Type) :=
  | Var_fo_term : ty'b3 -> fo_term ty'b0 ty'b3
  | App : symbol ty'b0 -> fo_term_list ty'b0 ty'b3 -> fo_term ty'b0 ty'b3.
Axiom fo_term_list_inhabited : forall  {ty'b0 : Type} `{Inhabited ty'b0} {ty'b3 : Type} `{Inhabited ty'b3}, Inhabited (fo_term_list ty'b0 ty'b3).
Global Existing Instance fo_term_list_inhabited.
Arguments FONil {ty'b0} {ty'b3}.
Arguments FOCons {ty'b0} {ty'b3}.
Axiom fo_term_inhabited : forall  {ty'b0 : Type} `{Inhabited ty'b0} {ty'b3 : Type} `{Inhabited ty'b3}, Inhabited (fo_term ty'b0 ty'b3).
Global Existing Instance fo_term_inhabited.
Arguments Var_fo_term {ty'b0} {ty'b3}.
Arguments App {ty'b0} {ty'b3}.
Axiom nat_size_fo_term_list : forall {ty'b3 : Type} `{Inhabited ty'b3} {ty'b0 : Type} `{Inhabited ty'b0}, fo_term_list ty'b0 ty'b3 -> Nat.nat.
Axiom nat_size_fo_term : forall {ty'b3 : Type} `{Inhabited ty'b3} {ty'b0 : Type} `{Inhabited ty'b0}, fo_term ty'b0 ty'b3 -> Nat.nat.
Axiom size_fo_term_list : forall {ty'b3 : Type} `{Inhabited ty'b3} {ty'b0 : Type} `{Inhabited ty'b0}, fo_term_list ty'b0 ty'b3 -> Z.
Axiom size_fo_term : forall {ty'b3 : Type} `{Inhabited ty'b3} {ty'b0 : Type} `{Inhabited ty'b0}, fo_term ty'b0 ty'b3 -> Z.
Axiom nat_size_fo_term_list_def : forall {ty'b3 : Type} {ty'b0 : Type} `{Inhabited ty'b3} `{Inhabited ty'b0} (t : fo_term_list ty'b0 ty'b3), nat_size_fo_term_list t = (match t with | FONil => (let s : Nat.nat := SNat ONat in s) | FOCons v0 v1 => (let s : Nat.nat := SNat ONat in let s1 : Nat.nat := add_nat (nat_size_fo_term_list v1) s in let s2 : Nat.nat := add_nat (nat_size_fo_term v0) s1 in s2) end).
Axiom nat_size_fo_term_def : forall {ty'b3 : Type} {ty'b0 : Type} `{Inhabited ty'b3} `{Inhabited ty'b0} (t : fo_term ty'b0 ty'b3), nat_size_fo_term t = (match t with | Var_fo_term v0 => SNat ONat | App v0 v1 => (let s : Nat.nat := SNat ONat in let s1 : Nat.nat := add_nat (nat_size_fo_term_list v1) s in let s2 : Nat.nat := add_nat (nat_size_symbol v0) s1 in s2) end).
Axiom size_fo_term_list_def : forall {ty'b3 : Type} {ty'b0 : Type} `{Inhabited ty'b3} `{Inhabited ty'b0} (t : fo_term_list ty'b0 ty'b3), size_fo_term_list t = (match t with | FONil => (let s : Z := 1%Z in s) | FOCons v0 v1 => (let s : Z := 1%Z in let s1 : Z := size_fo_term_list v1 + s in let s2 : Z := size_fo_term v0 + s1 in s2) end).
Axiom size_fo_term_def : forall {ty'b3 : Type} {ty'b0 : Type} `{Inhabited ty'b3} `{Inhabited ty'b0} (t : fo_term ty'b0 ty'b3), size_fo_term t = (match t with | Var_fo_term v0 => 1%Z | App v0 v1 => (let s : Z := 1%Z in let s1 : Z := size_fo_term_list v1 + s in let s2 : Z := size_symbol v0 + s1 in s2) end).
Axiom rename_fo_term_list : forall {ty'c0 : Type} `{Inhabited ty'c0} {ty'b3 : Type} `{Inhabited ty'b3} {ty'b0 : Type} `{Inhabited ty'b0} {ty'c3 : Type} `{Inhabited ty'c3}, fo_term_list ty'b0 ty'b3 -> (ty'b0 -> ty'c0) -> (ty'b3 -> ty'c3) -> fo_term_list ty'c0 ty'c3.
Axiom rename_fo_term : forall {ty'c0 : Type} `{Inhabited ty'c0} {ty'b3 : Type} `{Inhabited ty'b3} {ty'b0 : Type} `{Inhabited ty'b0} {ty'c3 : Type} `{Inhabited ty'c3}, fo_term ty'b0 ty'b3 -> (ty'b0 -> ty'c0) -> (ty'b3 -> ty'c3) -> fo_term ty'c0 ty'c3.
Axiom rename_fo_term_list_def : forall {ty'c0 : Type} {ty'b3 : Type} {ty'b0 : Type} {ty'c3 : Type} `{Inhabited ty'c0} `{Inhabited ty'b3} `{Inhabited ty'b0} `{Inhabited ty'c3} (t : fo_term_list ty'b0 ty'b3) (s0 : ty'b0 -> ty'c0) (s3 : ty'b3 -> ty'c3), rename_fo_term_list t s0 s3 = (match t with | FONil => (FONil : fo_term_list ty'c0 ty'c3) | FOCons v0 v1 => FOCons (rename_fo_term v0 s0 s3) (rename_fo_term_list v1 s0 s3) end).
Axiom rename_fo_term_def : forall {ty'c0 : Type} {ty'b3 : Type} {ty'b0 : Type} {ty'c3 : Type} `{Inhabited ty'c0} `{Inhabited ty'b3} `{Inhabited ty'b0} `{Inhabited ty'c3} (t : fo_term ty'b0 ty'b3) (s0 : ty'b0 -> ty'c0) (s3 : ty'b3 -> ty'c3), rename_fo_term t s0 s3 = (match t with | Var_fo_term v0 => Var_fo_term (s3 v0) | App v0 v1 => App (rename_symbol v0 s0) (rename_fo_term_list v1 s0 s3) end).
Axiom rename_subst_fo_term : forall {ty'b3 : Type} `{Inhabited ty'b3} {ty'c3 : Type} `{Inhabited ty'c3} {ty'c0 : Type} `{Inhabited ty'c0} {ty'd0 : Type} `{Inhabited ty'd0} {ty'd3 : Type} `{Inhabited ty'd3}, (ty'b3 -> fo_term ty'c0 ty'c3) -> (ty'c0 -> ty'd0) -> (ty'c3 -> ty'd3) -> ty'b3 -> fo_term ty'd0 ty'd3.
Axiom rename_subst_fo_term_definition : forall  {ty'b3 : Type} {ty'c3 : Type} {ty'c0 : Type} {ty'd0 : Type} {ty'd3 : Type} `{Inhabited ty'b3} `{Inhabited ty'c3} `{Inhabited ty'c0} `{Inhabited ty'd0} `{Inhabited ty'd3} (s0 : ty'b3 -> fo_term ty'c0 ty'c3) (s10 : ty'c0 -> ty'd0) (s13 : ty'c3 -> ty'd3) (x : ty'b3), rename_subst_fo_term s0 s10 s13 x = rename_fo_term (s0 x) s10 s13.
Definition olifts_fo_term {ty'c0 : Type} {ty'b3 : Type} {ty'c3 : Type} `{Inhabited ty'c0} `{Inhabited ty'b3} `{Inhabited ty'c3} (s : ty'b3 -> fo_term ty'c0 ty'c3) : option ty'b3 -> fo_term ty'c0 (option ty'c3) := ocase (rename_subst_fo_term s identity some) (Var_fo_term (None : option ty'c3)).
Axiom subst_fo_term_list : forall {ty'c0 : Type} `{Inhabited ty'c0} {ty'b3 : Type} `{Inhabited ty'b3} {ty'b0 : Type} `{Inhabited ty'b0} {ty'c3 : Type} `{Inhabited ty'c3}, fo_term_list ty'b0 ty'b3 -> (ty'b0 -> symbol ty'c0) -> (ty'b3 -> fo_term ty'c0 ty'c3) -> fo_term_list ty'c0 ty'c3.
Axiom subst_fo_term : forall {ty'c0 : Type} `{Inhabited ty'c0} {ty'b3 : Type} `{Inhabited ty'b3} {ty'b0 : Type} `{Inhabited ty'b0} {ty'c3 : Type} `{Inhabited ty'c3}, fo_term ty'b0 ty'b3 -> (ty'b0 -> symbol ty'c0) -> (ty'b3 -> fo_term ty'c0 ty'c3) -> fo_term ty'c0 ty'c3.
Axiom subst_fo_term_list_def : forall {ty'c0 : Type} {ty'b3 : Type} {ty'b0 : Type} {ty'c3 : Type} `{Inhabited ty'c0} `{Inhabited ty'b3} `{Inhabited ty'b0} `{Inhabited ty'c3} (t : fo_term_list ty'b0 ty'b3) (s0 : ty'b0 -> symbol ty'c0) (s3 : ty'b3 -> fo_term ty'c0 ty'c3), subst_fo_term_list t s0 s3 = (match t with | FONil => (FONil : fo_term_list ty'c0 ty'c3) | FOCons v0 v1 => FOCons (subst_fo_term v0 (rename_subst_symbol s0 identity) (rename_subst_fo_term s3 identity identity)) (subst_fo_term_list v1 (rename_subst_symbol s0 identity) (rename_subst_fo_term s3 identity identity)) end).
Axiom subst_fo_term_def : forall {ty'c0 : Type} {ty'b3 : Type} {ty'b0 : Type} {ty'c3 : Type} `{Inhabited ty'c0} `{Inhabited ty'b3} `{Inhabited ty'b0} `{Inhabited ty'c3} (t : fo_term ty'b0 ty'b3) (s0 : ty'b0 -> symbol ty'c0) (s3 : ty'b3 -> fo_term ty'c0 ty'c3), subst_fo_term t s0 s3 = (match t with | Var_fo_term v0 => s3 v0 | App v0 v1 => App (subst_symbol v0 (rename_subst_symbol s0 identity)) (subst_fo_term_list v1 (rename_subst_symbol s0 identity) (rename_subst_fo_term s3 identity identity)) end).
Axiom subst_compose_fo_term : forall {ty'b3 : Type} `{Inhabited ty'b3} {ty'c3 : Type} `{Inhabited ty'c3} {ty'c0 : Type} `{Inhabited ty'c0} {ty'd0 : Type} `{Inhabited ty'd0} {ty'd3 : Type} `{Inhabited ty'd3}, (ty'b3 -> fo_term ty'c0 ty'c3) -> (ty'c0 -> symbol ty'd0) -> (ty'c3 -> fo_term ty'd0 ty'd3) -> ty'b3 -> fo_term ty'd0 ty'd3.
Axiom subst_compose_fo_term_definition : forall  {ty'b3 : Type} {ty'c3 : Type} {ty'c0 : Type} {ty'd0 : Type} {ty'd3 : Type} `{Inhabited ty'b3} `{Inhabited ty'c3} `{Inhabited ty'c0} `{Inhabited ty'd0} `{Inhabited ty'd3} (s0 : ty'b3 -> fo_term ty'c0 ty'c3) (s10 : ty'c0 -> symbol ty'd0) (s13 : ty'c3 -> fo_term ty'd0 ty'd3) (x : ty'b3), subst_compose_fo_term s0 s10 s13 x = subst_fo_term (s0 x) s10 s13.
Axiom subst_id_fo_term : forall {ty'b3 : Type} `{Inhabited ty'b3} {ty'b0 : Type} `{Inhabited ty'b0}, ty'b3 -> fo_term ty'b0 ty'b3.
Axiom subst_id_fo_term_definition : forall  {ty'b3 : Type} {ty'b0 : Type} `{Inhabited ty'b3} `{Inhabited ty'b0} (x : ty'b3), (subst_id_fo_term : ty'b3 -> fo_term ty'b0 ty'b3) x = Var_fo_term x.
Axiom is_symbol_free_var_in_fo_term_list : forall {ty'b3 : Type} `{Inhabited ty'b3} {ty'b0 : Type} `{Inhabited ty'b0}, ty'b0 -> fo_term_list ty'b0 ty'b3 -> Prop.
Axiom is_fo_term_free_var_in_fo_term_list : forall {ty'b3 : Type} `{Inhabited ty'b3} {ty'b0 : Type} `{Inhabited ty'b0}, ty'b3 -> fo_term_list ty'b0 ty'b3 -> Prop.
Axiom is_symbol_free_var_in_fo_term : forall {ty'b3 : Type} `{Inhabited ty'b3} {ty'b0 : Type} `{Inhabited ty'b0}, ty'b0 -> fo_term ty'b0 ty'b3 -> Prop.
Axiom is_fo_term_free_var_in_fo_term : forall {ty'b3 : Type} `{Inhabited ty'b3} {ty'b0 : Type} `{Inhabited ty'b0}, ty'b3 -> fo_term ty'b0 ty'b3 -> Prop.
Axiom is_symbol_free_var_in_fo_term_list_def : forall {ty'b3 : Type} {ty'b0 : Type} `{Inhabited ty'b3} `{Inhabited ty'b0} (x : ty'b0) (t : fo_term_list ty'b0 ty'b3), is_symbol_free_var_in_fo_term_list x t = (match t with | FONil => False | FOCons v0 v1 => is_symbol_free_var_in_fo_term x v0 ∨ is_symbol_free_var_in_fo_term_list x v1 end).
Axiom is_fo_term_free_var_in_fo_term_list_def : forall {ty'b3 : Type} {ty'b0 : Type} `{Inhabited ty'b3} `{Inhabited ty'b0} (x : ty'b3) (t : fo_term_list ty'b0 ty'b3), is_fo_term_free_var_in_fo_term_list x t = (match t with | FONil => False | FOCons v0 v1 => is_fo_term_free_var_in_fo_term x v0 ∨ is_fo_term_free_var_in_fo_term_list x v1 end).
Axiom is_symbol_free_var_in_fo_term_def : forall {ty'b3 : Type} {ty'b0 : Type} `{Inhabited ty'b3} `{Inhabited ty'b0} (x : ty'b0) (t : fo_term ty'b0 ty'b3), is_symbol_free_var_in_fo_term x t = (match t with | Var_fo_term v0 => False | App v0 v1 => is_symbol_free_var_in_symbol x v0 ∨ is_symbol_free_var_in_fo_term_list x v1 end).
Axiom is_fo_term_free_var_in_fo_term_def : forall {ty'b3 : Type} {ty'b0 : Type} `{Inhabited ty'b3} `{Inhabited ty'b0} (x : ty'b3) (t : fo_term ty'b0 ty'b3), is_fo_term_free_var_in_fo_term x t = (match t with | Var_fo_term v0 => v0 = x | App v0 v1 => is_fo_term_free_var_in_fo_term_list x v1 end).
