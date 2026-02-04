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
Require Import prover.Firstorder_symbol_impl.Types.
Require Import prover.Firstorder_symbol_impl.Logic.
Require Import prover.Firstorder_symbol_impl.Impl.
Require Import prover.Firstorder_term_spec.Spec.
Open Scope Z_scope.
Inductive nl_fo_term_list (ty'b0 : Type) (ty'b3 : Type) :=
  | NL_FONil : nl_fo_term_list ty'b0 ty'b3
  | NL_FOCons : nl_fo_term ty'b0 ty'b3 -> nl_fo_term_list ty'b0 ty'b3 -> nl_fo_term_list ty'b0 ty'b3
with nl_fo_term (ty'b0 : Type) (ty'b3 : Type) :=
  | NLFVar_fo_term : ty'b3 -> nl_fo_term ty'b0 ty'b3
  | NLBruijn_fo_term : Z -> nl_fo_term ty'b0 ty'b3
  | NL_App : nl_symbol ty'b0 -> nl_fo_term_list ty'b0 ty'b3 -> nl_fo_term ty'b0 ty'b3.
Axiom nl_fo_term_list_inhabited : forall  {ty'b0 : Type} `{Inhabited ty'b0} {ty'b3 : Type} `{Inhabited ty'b3}, Inhabited (nl_fo_term_list ty'b0 ty'b3).
Global Existing Instance nl_fo_term_list_inhabited.
Arguments NL_FONil {ty'b0} {ty'b3}.
Arguments NL_FOCons {ty'b0} {ty'b3}.
Axiom nl_fo_term_inhabited : forall  {ty'b0 : Type} `{Inhabited ty'b0} {ty'b3 : Type} `{Inhabited ty'b3}, Inhabited (nl_fo_term ty'b0 ty'b3).
Global Existing Instance nl_fo_term_inhabited.
Arguments NLFVar_fo_term {ty'b0} {ty'b3}.
Arguments NLBruijn_fo_term {ty'b0} {ty'b3}.
Arguments NL_App {ty'b0} {ty'b3}.
Inductive nlimpl_fo_term_list :=
  | nlimpl_fo_term_list'mk : nl_fo_term_list Z Z -> Z -> Z -> fo_term_list Z Z -> nlimpl_fo_term_list.
Axiom nlimpl_fo_term_list_inhabited : Inhabited nlimpl_fo_term_list.
Global Existing Instance nlimpl_fo_term_list_inhabited.
Axiom nlimpl_fo_term_list_countable : Countable nlimpl_fo_term_list.
Global Existing Instance nlimpl_fo_term_list_countable.
Definition nlrepr_fo_term_list_field (x : nlimpl_fo_term_list) := match x with |  nlimpl_fo_term_list'mk a _ _ _ => a end.
Definition nlfree_var_symbol_set_abstraction_fo_term_list_field (x : nlimpl_fo_term_list) := match x with |  nlimpl_fo_term_list'mk _ a _ _ => a end.
Definition nlfree_var_fo_term_set_abstraction_fo_term_list_field (x : nlimpl_fo_term_list) := match x with |  nlimpl_fo_term_list'mk _ _ a _ => a end.
Definition model_fo_term_list_field (x : nlimpl_fo_term_list) := match x with |  nlimpl_fo_term_list'mk _ _ _ a => a end.
Inductive nlimpl_fo_term :=
  | nlimpl_fo_term'mk : nl_fo_term Z Z -> Z -> Z -> fo_term Z Z -> nlimpl_fo_term.
Axiom nlimpl_fo_term_inhabited : Inhabited nlimpl_fo_term.
Global Existing Instance nlimpl_fo_term_inhabited.
Axiom nlimpl_fo_term_countable : Countable nlimpl_fo_term.
Global Existing Instance nlimpl_fo_term_countable.
Definition nlrepr_fo_term_field (x : nlimpl_fo_term) := match x with |  nlimpl_fo_term'mk a _ _ _ => a end.
Definition nlfree_var_symbol_set_abstraction_fo_term_field (x : nlimpl_fo_term) := match x with |  nlimpl_fo_term'mk _ a _ _ => a end.
Definition nlfree_var_fo_term_set_abstraction_fo_term_field (x : nlimpl_fo_term) := match x with |  nlimpl_fo_term'mk _ _ a _ => a end.
Definition model_fo_term_field (x : nlimpl_fo_term) := match x with |  nlimpl_fo_term'mk _ _ _ a => a end.
Inductive cons_fo_term_list :=
  | NLC_FONil : cons_fo_term_list
  | NLC_FOCons : nlimpl_fo_term -> nlimpl_fo_term_list -> cons_fo_term_list.
Axiom cons_fo_term_list_inhabited : Inhabited cons_fo_term_list.
Global Existing Instance cons_fo_term_list_inhabited.
Axiom cons_fo_term_list_countable : Countable cons_fo_term_list.
Global Existing Instance cons_fo_term_list_countable.
Inductive cons_fo_term :=
  | NLCVar_fo_term : Z -> cons_fo_term
  | NLC_App : nlimpl_symbol -> nlimpl_fo_term_list -> cons_fo_term.
Axiom cons_fo_term_inhabited : Inhabited cons_fo_term.
Global Existing Instance cons_fo_term_inhabited.
Axiom cons_fo_term_countable : Countable cons_fo_term.
Global Existing Instance cons_fo_term_countable.
