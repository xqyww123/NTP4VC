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
Inductive nl_symbol (ty'b0 : Type) :=
  | NLFVar_symbol : ty'b0 -> nl_symbol ty'b0
  | NLBruijn_symbol : Z -> nl_symbol ty'b0.
Axiom nl_symbol_inhabited : forall  {ty'b0 : Type} `{Inhabited ty'b0}, Inhabited (nl_symbol ty'b0).
Global Existing Instance nl_symbol_inhabited.
Arguments NLFVar_symbol {ty'b0}.
Arguments NLBruijn_symbol {ty'b0}.
Inductive nlimpl_symbol :=
  | nlimpl_symbol'mk : nl_symbol Z -> Z -> symbol Z -> nlimpl_symbol.
Axiom nlimpl_symbol_inhabited : Inhabited nlimpl_symbol.
Global Existing Instance nlimpl_symbol_inhabited.
Axiom nlimpl_symbol_countable : Countable nlimpl_symbol.
Global Existing Instance nlimpl_symbol_countable.
Definition nlrepr_symbol_field (x : nlimpl_symbol) := match x with |  nlimpl_symbol'mk a _ _ => a end.
Definition nlfree_var_symbol_set_abstraction_symbol_field (x : nlimpl_symbol) := match x with |  nlimpl_symbol'mk _ a _ => a end.
Definition model_symbol_field (x : nlimpl_symbol) := match x with |  nlimpl_symbol'mk _ _ a => a end.
Inductive cons_symbol :=
  | NLCVar_symbol : Z -> cons_symbol.
Axiom cons_symbol_inhabited : Inhabited cons_symbol.
Global Existing Instance cons_symbol_inhabited.
Axiom cons_symbol_countable : Countable cons_symbol.
Global Existing Instance cons_symbol_countable.
