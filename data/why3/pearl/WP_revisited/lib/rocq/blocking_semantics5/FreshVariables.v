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
Require Import WP_revisited.blocking_semantics5.Syntax.
Require Import WP_revisited.blocking_semantics5.SemOp.
Open Scope Z_scope.
Program Fixpoint msubst_term (t : term) (x : mident) (v : ident) : term :=
match t with | Tvalue _ => t | Tvar _ => t | Tderef y => (if decide (x = y) then Tvar v else t) | Tbin t1 op t2 => Tbin (msubst_term t1 x v) op (msubst_term t2 x v) end.
Admit Obligations.
Program Fixpoint msubst (f : fmla) (x : mident) (v : ident) : fmla :=
match f with | Fterm e => Fterm (msubst_term e x v) | Fand f1 f2 => Fand (msubst f1 x v) (msubst f2 x v) | Fnot f1 => Fnot (msubst f1 x v) | Fimplies f1 f2 => Fimplies (msubst f1 x v) (msubst f2 x v) | Flet y t f1 => Flet y (msubst_term t x v) (msubst f1 x v) | Fforall y ty f1 => Fforall y ty (msubst f1 x v) end.
Admit Obligations.
Program Fixpoint fresh_in_term (id1 : ident) (t : term) : Prop :=
match t with | Tvalue _ => True | Tderef _ => True | Tvar i => ¬ id1 = i | Tbin t1 _ t2 => fresh_in_term id1 t1 ∧ fresh_in_term id1 t2 end.
Admit Obligations.
Program Fixpoint fresh_in_fmla (id1 : ident) (f : fmla) : Prop :=
match f with | Fterm e => fresh_in_term id1 e | Fand f1 f2 => fresh_in_fmla id1 f1 ∧ fresh_in_fmla id1 f2 | Fimplies f1 f2 => fresh_in_fmla id1 f1 ∧ fresh_in_fmla id1 f2 | Fnot f1 => fresh_in_fmla id1 f1 | Flet y t f1 => ¬ id1 = y ∧ fresh_in_term id1 t ∧ fresh_in_fmla id1 f1 | Fforall y _ f1 => ¬ id1 = y ∧ fresh_in_fmla id1 f1 end.
Admit Obligations.
