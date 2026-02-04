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
Open Scope Z_scope.
Axiom model : Type.
Axiom model_inhabited : Inhabited model.
Global Existing Instance model_inhabited.
Axiom model_countable : Countable model.
Global Existing Instance model_countable.
Axiom t : Type.
Axiom t_inhabited : Inhabited t.
Global Existing Instance t_inhabited.
Axiom t_countable : Countable t.
Global Existing Instance t_countable.
Axiom model1 : t -> program_var -> option svar.
Axiom empty : t.
Axiom empty1 : forall  (k : program_var), model1 empty k = None.
Definition get (d : t) (k : program_var) : option svar := model1 d k.
Axiom set : t -> program_var -> svar -> t.
Axiom set'spec'0 : forall  (d : t) (k : program_var) (v : svar), get (set d k v) k = Some v.
Axiom set'spec : forall  (k' : program_var) (k : program_var) (d : t) (v : svar) (fact0 : ¬ k' = k), get (set d k v) k' = get d k'.
Axiom rho : Type.
Axiom rho_inhabited : Inhabited rho.
Global Existing Instance rho_inhabited.
Axiom rho_countable : Countable rho.
Global Existing Instance rho_countable.
Inductive symbolic_expr :=
  | Slit : Z -> symbolic_expr
  | Svar : svar -> symbolic_expr
  | Ssub : symbolic_expr -> symbolic_expr -> symbolic_expr.
Axiom symbolic_expr_inhabited : Inhabited symbolic_expr.
Global Existing Instance symbolic_expr_inhabited.
Axiom symbolic_expr_countable : Countable symbolic_expr.
Global Existing Instance symbolic_expr_countable.
Program Fixpoint interp_symbolic_expr (rho1 : svar -> Z) (e : symbolic_expr) : Z :=
match e with | Slit n => n | Svar v => rho1 v | Ssub e1 e2 => interp_symbolic_expr rho1 e1 - interp_symbolic_expr rho1 e2 end.
Admit Obligations.
Inductive constr :=
  | Ctrue : constr
  | Cfalse : constr
  | Ceq : symbolic_expr -> symbolic_expr -> constr
  | Cneq : symbolic_expr -> symbolic_expr -> constr
  | Cconj : constr -> constr -> constr
  | Cexists : svar -> constr -> constr.
Axiom constr_inhabited : Inhabited constr.
Global Existing Instance constr_inhabited.
Axiom constr_countable : Countable constr.
Global Existing Instance constr_countable.
Program Fixpoint is_solution (rho1 : svar -> Z) (c : constr) : Prop :=
match c with | Ctrue => True | Cfalse => False | Ceq e1 e2 => interp_symbolic_expr rho1 e1 = interp_symbolic_expr rho1 e2 | Cneq e1 e2 => ¬ interp_symbolic_expr rho1 e1 = interp_symbolic_expr rho1 e2 | Cconj c1 c2 => is_solution rho1 c1 ∧ is_solution rho1 c2 | Cexists _ c1 => is_solution rho1 c1 end.
Admit Obligations.
Program Fixpoint vars_in_symbolic_expr (e : symbolic_expr) : gset svar :=
match e with | Slit _ => (∅ : gset svar) | Svar v => ({[v]} : gset _) | Ssub e1 e2 => vars_in_symbolic_expr e1 ∪ vars_in_symbolic_expr e2 end.
Admit Obligations.
Program Fixpoint vars_in_constraint (c : constr) : gset svar :=
match c with | Ctrue => (∅ : gset svar) | Cfalse => (∅ : gset svar) | Ceq e1 e2 => vars_in_symbolic_expr e1 ∪ vars_in_symbolic_expr e2 | Cneq e1 e2 => vars_in_symbolic_expr e1 ∪ vars_in_symbolic_expr e2 | Cconj c1 c2 => vars_in_constraint c1 ∪ vars_in_constraint c2 | Cexists v c1 => insert_set v (vars_in_constraint c1) end.
Admit Obligations.
Program Fixpoint existential_vars_in_constraint (c : constr) : gset svar :=
match c with | Ctrue => (∅ : gset svar) | Cfalse => (∅ : gset svar) | Ceq e1 e2 => vars_in_symbolic_expr e1 ∪ vars_in_symbolic_expr e2 | Cneq e1 e2 => vars_in_symbolic_expr e1 ∪ vars_in_symbolic_expr e2 | Cconj c1 c2 => existential_vars_in_constraint c1 ∪ existential_vars_in_constraint c2 | Cexists v c1 => remove_set v (existential_vars_in_constraint c1) end.
Admit Obligations.
Definition free_vars_in_constraint (c : constr) : gset svar := vars_in_constraint c ∖ existential_vars_in_constraint c.
Definition entails (c1 : constr) (c2 : constr) := ∀(rho1 : svar -> Z), is_solution rho1 c1 -> is_solution rho1 c2.
