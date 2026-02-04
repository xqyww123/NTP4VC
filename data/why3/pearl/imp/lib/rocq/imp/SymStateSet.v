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
Require Import imp.imp.Syntax.
Require Import imp.imp.Svar.
Require Import imp.imp.Constraint.
Require Import imp.imp.SymState.
Open Scope Z_scope.
Axiom set : Type.
Axiom set_inhabited : Inhabited set.
Global Existing Instance set_inhabited.
Axiom set_countable : Countable set.
Global Existing Instance set_countable.
Axiom to_fset : set -> gset sym_state.
Axiom mk : gset sym_state -> set.
Axiom mk'spec : forall  (s : gset sym_state), to_fset (mk s) = s.
Axiom choose1 : set -> sym_state.
Axiom choose'spec : forall  (s : set) (fact0 : ¬ to_fset s = ∅), choose1 s ∈ to_fset s.
Axiom to_list : set -> list sym_state.
Axiom to_list'spec : forall  (e : sym_state) (s : set), (e ∈ to_fset s) = (e ∈ to_list s).
Axiom of_list : list sym_state -> set.
Axiom of_list'spec : forall  (e : sym_state) (l : list sym_state), (e ∈ to_fset (of_list l)) = (e ∈ l).
