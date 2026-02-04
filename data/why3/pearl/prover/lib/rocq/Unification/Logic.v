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
Require Import prover.Unification.Types.
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
Axiom sdata_inv : sdata -> bool.
Axiom sdata_inv_def : forall  (x : sdata), (sdata_inv x = true) = (match x with | PConflict l1 l2 => nlimpl_fo_term_list_ok l1 ∧ nlimpl_fo_term_list_ok l2 ∧ (∀(x1 : Z), is_fo_term_free_var_in_fo_term_list x1 (model_fo_term_list_field l1) -> 0%Z ≤ x1) ∧ (∀(x1 : Z), is_fo_term_free_var_in_fo_term_list x1 (model_fo_term_list_field l2) -> 0%Z ≤ x1) | Assign l => nlimpl_fo_term_ok l ∧ (∀(x1 : Z), is_fo_term_free_var_in_fo_term x1 (model_fo_term_field l) -> 0%Z ≤ x1) end).
Axiom smodel : timestamp sdata -> Z -> fo_term Z Z.
Axiom smodel_def : forall  (l : timestamp sdata) (x : Z), smodel l x = (match table l x with | [] => Var_fo_term x | cons (PConflict _ _) _ => Var_fo_term x | cons (Assign u) _ => model_fo_term_field u end).
Definition unassigned (l : timestamp sdata) (x : Z) := match table l x with | cons (Assign _) _ => False | _ => True end.
Definition unifier_subst_ok (rho : t sdata) (u : unifier_subst) := smodel (current_timestamp rho) = unifier_base_model u ∧ (∀(x : Z), unifier_base_model u x = Var_fo_term x -> unassigned (current_timestamp rho) x) ∧ (∀(x : Z), unifier_base_model u x = Var_fo_term x -> unifier u x = Var_fo_term x) ∧ subst_compose_fo_term (unifier_base_model u) subst_id_symbol (unifier u) = unifier u ∧ subst_compose_fo_term (unifier u) subst_id_symbol (unifier_base_model u) = unifier u ∧ subst_compose_fo_term (unifier u) subst_id_symbol (unifier u) = unifier u ∧ correct rho ∧ inv rho = sdata_inv.
