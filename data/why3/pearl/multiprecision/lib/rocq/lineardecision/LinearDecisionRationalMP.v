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
Require Import Why3.why3.Ref.Ref.
Require Import Why3.mach.matrix.Matrix63.
Require Import Why3.debug.Debug.
Require Import multiprecision.lineardecision.RationalCoeffs.
Require Import multiprecision.lineardecision.MP64Coeffs.
Open Scope Z_scope.
Axiom coeff : Type.
Axiom coeff_inhabited : Inhabited coeff.
Global Existing Instance coeff_inhabited.
Axiom coeff_countable : Countable coeff.
Global Existing Instance coeff_countable.
Axiom sub_def : forall  (a1 : R) (a2 : R), Rminus a1 a2 = Rplus a1 (Ropp a2).
Axiom vars : Type.
Axiom vars_inhabited : Inhabited vars.
Global Existing Instance vars_inhabited.
Axiom vars_countable : Countable vars.
Global Existing Instance vars_countable.
Axiom zero_def : forall  (y : Z -> Z), minterp ((0%Z, 1%Z), Lit 0%Z) y = 0%R.
Axiom one_def : forall  (y : Z -> Z), minterp ((1%Z, 1%Z), Lit 0%Z) y = 1%R.
Axiom vars1 : Type.
Axiom vars1_inhabited : Inhabited vars1.
Global Existing Instance vars1_inhabited.
Axiom vars1_countable : Countable vars1.
Global Existing Instance vars1_countable.
Inductive expr :=
  | Term : Z * Z * MP64Coeffs.exp -> Z -> expr
  | Add : expr -> expr -> expr
  | Cst : Z * Z * MP64Coeffs.exp -> expr.
Axiom expr_inhabited : Inhabited expr.
Global Existing Instance expr_inhabited.
Axiom expr_countable : Countable expr.
Global Existing Instance expr_countable.
Program Fixpoint valid_expr (e : expr) : Prop :=
match e with | Term _ i => 0%Z ≤ i | Cst _ => True | Add e1 e2 => valid_expr e1 ∧ valid_expr e2 end.
Admit Obligations.
Program Fixpoint expr_bound (e : expr) (b : Z) : Prop :=
match e with | Term _ i => 0%Z ≤ i ∧ i ≤ b | Cst _ => True | Add e1 e2 => expr_bound e1 b ∧ expr_bound e2 b end.
Admit Obligations.
Program Fixpoint interp (e : expr) (y : Z -> R) (z : Z -> Z) : R :=
match e with | Term c v => Rmult (minterp c z) (y v) | Add e1 e2 => Rplus (interp e1 y z) (interp e2 y z) | Cst c => minterp c z end.
Admit Obligations.
Axiom equality : Type.
Axiom equality_inhabited : Inhabited equality.
Global Existing Instance equality_inhabited.
Axiom equality_countable : Countable equality.
Global Existing Instance equality_countable.
Axiom context : Type.
Axiom context_inhabited : Inhabited context.
Global Existing Instance context_inhabited.
Axiom context_countable : Countable context.
Global Existing Instance context_countable.
Definition valid_eq (eq : expr * expr) := match eq with | (e1, e2) => valid_expr e1 ∧ valid_expr e2 end.
Definition eq_bound (eq : expr * expr) (b : Z) := match eq with | (e1, e2) => expr_bound e1 b ∧ expr_bound e2 b end.
Program Fixpoint valid_ctx (ctx : list (expr * expr)) : Prop :=
match ctx with | [] => True | cons eq t => valid_eq eq ∧ valid_ctx t end.
Admit Obligations.
Program Fixpoint ctx_bound (ctx : list (expr * expr)) (b : Z) : Prop :=
match ctx with | [] => True | cons eq t => eq_bound eq b ∧ ctx_bound t b end.
Admit Obligations.
Definition interp_eq (g : expr * expr) (y : Z -> R) (z : Z -> Z) : bool := if decide (match g with | (g1, g2) => interp g1 y z = interp g2 y z end) then true else false.
Program Fixpoint interp_ctx (l : list (expr * expr)) (g : expr * expr) (y : Z -> R) (z : Z -> Z) : bool :=
if decide (match l with | [] => interp_eq g y z = true | cons h t => interp_eq h y z = true -> interp_ctx t g y z = true end) then true else false.
Admit Obligations.
Axiom infix_eqeq : array63 (Z * Z * MP64Coeffs.exp) -> array63 (Z * Z * MP64Coeffs.exp) -> Prop.
Axiom infix_eqeq'spec : forall  (a : array63 (Z * Z * MP64Coeffs.exp)) (b : array63 (Z * Z * MP64Coeffs.exp)) (fact0 : infix_eqeq a b), array63_length a = array63_length b ∧ (∀(i : Z), 0%Z ≤ i ∧ i < bv_signed (array63_length a) -> meq (nth (Z.to_nat i) (array63_elts a) inhabitant) (nth (Z.to_nat i) (array63_elts b) inhabitant)).
Axiom max_var : expr -> Z.
Axiom max_var'def : forall  (e : expr) (fact0 : valid_expr e), match e with | Term _ i => max_var e = i | Cst _ => max_var e = 0%Z | Add e1 e2 => max_var e = Z.max (max_var e1) (max_var e2) end.
Axiom max_var'spec'0 : forall  (e : expr) (fact0 : valid_expr e), 0%Z ≤ max_var e.
Axiom max_var'spec : forall  (e : expr) (fact0 : valid_expr e), expr_bound e (max_var e).
Axiom max_var_e : expr * expr -> Z.
Axiom max_var_e'def : forall  (e : expr * expr) (fact0 : valid_eq e), match e with | (e1, e2) => max_var_e e = Z.max (max_var e1) (max_var e2) end.
Axiom max_var_e'spec'0 : forall  (e : expr * expr) (fact0 : valid_eq e), 0%Z ≤ max_var_e e.
Axiom max_var_e'spec : forall  (e : expr * expr) (fact0 : valid_eq e), eq_bound e (max_var_e e).
Axiom max_var_ctx : list (expr * expr) -> Z.
Axiom max_var_ctx'def : forall  (l : list (expr * expr)) (fact0 : valid_ctx l), match l with | [] => max_var_ctx l = 0%Z | cons e t => max_var_ctx l = Z.max (max_var_e e) (max_var_ctx t) end.
Axiom max_var_ctx'spec'0 : forall  (l : list (expr * expr)) (fact0 : valid_ctx l), 0%Z ≤ max_var_ctx l.
Axiom max_var_ctx'spec : forall  (l : list (expr * expr)) (fact0 : valid_ctx l), ctx_bound l (max_var_ctx l).
Definition atom (e : expr) := match e with | Add _ _ => False | _ => True end.
Axiom to_list : forall {α : Type} `{Inhabited α}, array63 α -> bv 63%N -> bv 63%N -> list α.
Inductive expr' :=
  | Sum : expr' -> expr' -> expr'
  | ProdL : expr' -> cprod -> expr'
  | ProdR : cprod -> expr' -> expr'
  | Diff : expr' -> expr' -> expr'
  | Var : Z -> expr'
  | Coeff : Z * Z * MP64Coeffs.exp -> expr'
with cprod :=
  | C : Z * Z * MP64Coeffs.exp -> cprod
  | Times : cprod -> cprod -> cprod.
Axiom expr'_inhabited : Inhabited expr'.
Global Existing Instance expr'_inhabited.
Axiom expr'_countable : Countable expr'.
Global Existing Instance expr'_countable.
Axiom cprod_inhabited : Inhabited cprod.
Global Existing Instance cprod_inhabited.
Axiom cprod_countable : Countable cprod.
Global Existing Instance cprod_countable.
Program Fixpoint interp_c (e : cprod) (y : Z -> R) (z : Z -> Z) : R :=
match e with | C c => minterp c z | Times e1 e2 => Rmult (interp_c e1 y z) (interp_c e2 y z) end.
Admit Obligations.
Program Fixpoint interp' (e : expr') (y : Z -> R) (z : Z -> Z) : R :=
match e with | Sum e1 e2 => Rplus (interp' e1 y z) (interp' e2 y z) | ProdL e1 c => Rmult (interp' e1 y z) (interp_c c y z) | ProdR c e1 => Rmult (interp_c c y z) (interp' e1 y z) | Diff e1 e2 => Rminus (interp' e1 y z) (interp' e2 y z) | Var n => y n | Coeff c => minterp c z end.
Admit Obligations.
Axiom equality' : Type.
Axiom equality'_inhabited : Inhabited equality'.
Global Existing Instance equality'_inhabited.
Axiom equality'_countable : Countable equality'.
Global Existing Instance equality'_countable.
Axiom context' : Type.
Axiom context'_inhabited : Inhabited context'.
Global Existing Instance context'_inhabited.
Axiom context'_countable : Countable context'.
Global Existing Instance context'_countable.
Definition interp_eq' (g : expr' * expr') (y : Z -> R) (z : Z -> Z) : bool := if decide (match g with | (g1, g2) => interp' g1 y z = interp' g2 y z end) then true else false.
Program Fixpoint interp_ctx' (l : list (expr' * expr')) (g : expr' * expr') (y : Z -> R) (z : Z -> Z) : bool :=
if decide (match l with | [] => interp_eq' g y z = true | cons h t => interp_eq' h y z = true -> interp_ctx' t g y z = true end) then true else false.
Admit Obligations.
Program Fixpoint valid_expr' (e : expr') : Prop :=
match e with | Var i => 0%Z ≤ i | Sum e1 e2 => valid_expr' e1 ∧ valid_expr' e2 | Diff e1 e2 => valid_expr' e1 ∧ valid_expr' e2 | Coeff _ => True | ProdL e1 _ => valid_expr' e1 | ProdR _ e1 => valid_expr' e1 end.
Admit Obligations.
Definition valid_eq' (eq : expr' * expr') := match eq with | (e1, e2) => valid_expr' e1 ∧ valid_expr' e2 end.
Program Fixpoint valid_ctx' (ctx : list (expr' * expr')) : Prop :=
match ctx with | [] => True | cons eq t => valid_eq' eq ∧ valid_ctx' t end.
Admit Obligations.
