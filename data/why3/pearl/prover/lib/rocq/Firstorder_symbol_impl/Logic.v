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
Require Import prover.Firstorder_symbol_impl.Types.
Require Import prover.Nat.Nat.
Require Import prover.Functions.Config.
Require Import prover.Functions.Func.
Require Import prover.OptionFuncs.Funcs.
Require Import prover.Sum.Sum.
Require Import prover.Firstorder_symbol_spec.Spec.
Open Scope Z_scope.
Axiom nat_nlsize_symbol : forall {ty'b0 : Type} `{Inhabited ty'b0}, nl_symbol ty'b0 -> Nat.nat.
Axiom nlsize_symbol : forall {ty'b0 : Type} `{Inhabited ty'b0}, nl_symbol ty'b0 -> Z.
Axiom nat_nlsize_symbol_def : forall {ty'b0 : Type} `{Inhabited ty'b0} (t : nl_symbol ty'b0), nat_nlsize_symbol t = (match t with | NLFVar_symbol v0 => SNat ONat | NLBruijn_symbol v0 => SNat ONat end).
Axiom nlsize_symbol_def : forall {ty'b0 : Type} `{Inhabited ty'b0} (t : nl_symbol ty'b0), nlsize_symbol t = (match t with | NLFVar_symbol v0 => 1%Z | NLBruijn_symbol v0 => 1%Z end).
Axiom shiftb_symbol : forall {ty'b0 : Type} `{Inhabited ty'b0}, (Z -> symbol ty'b0) -> Z -> symbol (option ty'b0).
Axiom shiftb_symbol_definition : forall  {ty'b0 : Type} `{Inhabited ty'b0} (bnd : Z -> symbol ty'b0) (i : Z), shiftb_symbol bnd i = (if decide (i = 0%Z) then Var_symbol (None : option ty'b0) else rename_symbol (bnd (i - 1%Z)) some).
Definition nlmodel_symbol {ty'b0 : Type} {ty'c0 : Type} `{Inhabited ty'b0} `{Inhabited ty'c0} (t : nl_symbol ty'b0) (fr0 : ty'b0 -> symbol ty'c0) (bnd0 : Z -> symbol ty'c0) : symbol ty'c0 := match t with | NLFVar_symbol v0 => fr0 v0 | NLBruijn_symbol v0 => bnd0 v0 end.
Definition correct_indexes_symbol {ty'b0 : Type} `{Inhabited ty'b0} (t : nl_symbol ty'b0) := match t with | NLFVar_symbol v0 => True | NLBruijn_symbol v0 => 0%Z ≤ v0 end.
Definition bound_depth_of_symbol_in_symbol {ty'b0 : Type} `{Inhabited ty'b0} (t : nl_symbol ty'b0) : Z := match t with | NLFVar_symbol v0 => 0%Z | NLBruijn_symbol v0 => 1%Z + v0 end.
Definition nlimpl_symbol_ok (t : nlimpl_symbol) := nlmodel_symbol (nlrepr_symbol_field t) subst_id_symbol ((const : symbol Z -> Z -> symbol Z) (Var_symbol (- 1%Z))) = model_symbol_field t ∧ correct_indexes_symbol (nlrepr_symbol_field t) ∧ bound_depth_of_symbol_in_symbol (nlrepr_symbol_field t) = 0%Z ∧ (∀(x : Z), is_symbol_free_var_in_symbol x (model_symbol_field t) -> x < nlfree_var_symbol_set_abstraction_symbol_field t).
Definition cons_ok_symbol (c : cons_symbol) := match c with | NLCVar_symbol v0 => True end.
Definition cons_rel_symbol (c : cons_symbol) (t : nlimpl_symbol) := match c with | NLCVar_symbol v0 => model_symbol_field t = Var_symbol v0 end.
Definition cons_open_rel_symbol (c : cons_symbol) (t : nlimpl_symbol) := match c with | NLCVar_symbol v0 => model_symbol_field t = Var_symbol v0 end.
