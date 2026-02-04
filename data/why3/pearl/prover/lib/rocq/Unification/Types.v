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
Require Import prover.BacktrackArray.Types.
Require Import prover.Predicates.Pred.
Require Import prover.BacktrackArray.Logic.
Require Import prover.Choice.Choice.
Require Import prover.BacktrackArray.Impl.
Require Import prover.Firstorder_symbol_spec.Spec.
Require Import prover.Nat.Nat.
Require Import prover.OptionFuncs.Funcs.
Require Import prover.Sum.Sum.
Require Import prover.Firstorder_symbol_impl.Types.
Require Import prover.Firstorder_symbol_impl.Logic.
Require Import prover.Firstorder_symbol_impl.Impl.
Require Import prover.Firstorder_term_spec.Spec.
Require Import prover.Firstorder_term_impl.Types.
Require Import prover.Firstorder_term_impl.Logic.
Require Import prover.Firstorder_term_impl.Impl.
Open Scope Z_scope.
Inductive sdata :=
  | PConflict : nlimpl_fo_term_list -> nlimpl_fo_term_list -> sdata
  | Assign : nlimpl_fo_term -> sdata.
Axiom sdata_inhabited : Inhabited sdata.
Global Existing Instance sdata_inhabited.
Axiom sdata_countable : Countable sdata.
Global Existing Instance sdata_countable.
Axiom subst : Type.
Axiom subst_inhabited : Inhabited subst.
Global Existing Instance subst_inhabited.
Axiom subst_countable : Countable subst.
Global Existing Instance subst_countable.
Axiom timesubst : Type.
Axiom timesubst_inhabited : Inhabited timesubst.
Global Existing Instance timesubst_inhabited.
Axiom timesubst_countable : Countable timesubst.
Global Existing Instance timesubst_countable.
Inductive unifier_subst :=
  | unifier_subst'mk : (Z -> fo_term Z Z) -> (Z -> fo_term Z Z) -> unifier_subst.
Axiom unifier_subst_inhabited : Inhabited unifier_subst.
Global Existing Instance unifier_subst_inhabited.
Axiom unifier_subst_countable : Countable unifier_subst.
Global Existing Instance unifier_subst_countable.
Definition unifier_base_model (x : unifier_subst) := match x with |  unifier_subst'mk a _ => a end.
Definition unifier (x : unifier_subst) := match x with |  unifier_subst'mk _ a => a end.
Inductive unification_return :=
  | unification_return'mk : unifier_subst -> (Z -> fo_term Z Z) -> unification_return.
Axiom unification_return_inhabited : Inhabited unification_return.
Global Existing Instance unification_return_inhabited.
Axiom unification_return_countable : Countable unification_return.
Global Existing Instance unification_return_countable.
Definition final_unifier (x : unification_return) := match x with |  unification_return'mk a _ => a end.
Definition unifier_factor (x : unification_return) := match x with |  unification_return'mk _ a => a end.
