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
Open Scope Z_scope.
Axiom sym_state : Type.
Axiom sym_state_inhabited : Inhabited sym_state.
Global Existing Instance sym_state_inhabited.
Axiom sym_state_countable : Countable sym_state.
Global Existing Instance sym_state_countable.
Axiom sigma : sym_state -> t.
Axiom constr : sym_state -> Constraint.constr.
Axiom rho : sym_state -> svar -> Z.
Axiom vars : sym_state -> Svar.set.
Axiom sym_state'invariant : forall  (self : sym_state), vars_in_constraint (constr self) ⊆ to_fset (vars self) ∧ (∀(x : program_var) (v : svar), get (sigma self) x = Some v -> v ∈ to_fset (vars self)).
Definition sym_state'eq (a : sym_state) (b : sym_state) := sigma a = sigma b ∧ constr a = constr b ∧ rho a = rho b ∧ vars a = vars b.
Axiom sym_state'inj : forall  (a : sym_state) (b : sym_state) (fact0 : sym_state'eq a b), a = b.
Axiom eq : sym_state -> sym_state -> Prop.
Axiom eq'spec : forall  (s1 : sym_state) (s2 : sym_state), eq s1 s2 = (s1 = s2).
Axiom mk_sym_state : t -> Constraint.constr -> Svar.set -> (svar -> Z) -> sym_state.
Axiom mk_sym_state'spec'2 : forall  (constr1 : Constraint.constr) (vars1 : Svar.set) (sigma1 : t) (rho1 : svar -> Z) (fact0 : vars_in_constraint constr1 ⊆ to_fset vars1) (fact1 : ∀(x : program_var) (v : svar), get sigma1 x = Some v -> v ∈ to_fset vars1), sigma (mk_sym_state sigma1 constr1 vars1 rho1) = sigma1.
Axiom mk_sym_state'spec'1 : forall  (constr1 : Constraint.constr) (vars1 : Svar.set) (sigma1 : t) (rho1 : svar -> Z) (fact0 : vars_in_constraint constr1 ⊆ to_fset vars1) (fact1 : ∀(x : program_var) (v : svar), get sigma1 x = Some v -> v ∈ to_fset vars1), constr (mk_sym_state sigma1 constr1 vars1 rho1) = constr1.
Axiom mk_sym_state'spec'0 : forall  (constr1 : Constraint.constr) (vars1 : Svar.set) (sigma1 : t) (rho1 : svar -> Z) (fact0 : vars_in_constraint constr1 ⊆ to_fset vars1) (fact1 : ∀(x : program_var) (v : svar), get sigma1 x = Some v -> v ∈ to_fset vars1), vars (mk_sym_state sigma1 constr1 vars1 rho1) = vars1.
Axiom mk_sym_state'spec : forall  (constr1 : Constraint.constr) (vars1 : Svar.set) (sigma1 : t) (rho1 : svar -> Z) (fact0 : vars_in_constraint constr1 ⊆ to_fset vars1) (fact1 : ∀(x : program_var) (v : svar), get sigma1 x = Some v -> v ∈ to_fset vars1), rho (mk_sym_state sigma1 constr1 vars1 rho1) = rho1.
