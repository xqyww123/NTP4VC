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
Require Import Why3.int.NumOf.
Require Import Why3.mach.matrix.Matrix63.
Require Import Why3.debug.Debug.
Require Import multiprecision.lineardecision.RationalCoeffs.
Require Import multiprecision.lineardecision.MP64Coeffs.
Require Import multiprecision.lineardecision.LinearDecisionRationalMP.
Require Import multiprecision.lineardecision.LinearDecisionIntMP.
Open Scope Z_scope.
Program Fixpoint expr_bound' (e : LinearDecisionIntMP.expr') (b : Z) : Prop :=
match e with | LinearDecisionIntMP.Sum e1 e2 => expr_bound' e1 b ∧ expr_bound' e2 b | LinearDecisionIntMP.Diff e1 e2 => expr_bound' e1 b ∧ expr_bound' e2 b | LinearDecisionIntMP.ProdL e1 _ => expr_bound' e1 b | LinearDecisionIntMP.ProdR _ e1 => expr_bound' e1 b | LinearDecisionIntMP.Var n => 0%Z ≤ n ∧ n ≤ b | LinearDecisionIntMP.Coeff _ => True end.
Admit Obligations.
Definition eq_bound' (eq : LinearDecisionIntMP.expr' * LinearDecisionIntMP.expr') (b : Z) := match eq with | (e1, e2) => expr_bound' e1 b ∧ expr_bound' e2 b end.
Program Fixpoint ctx_bound' (ctx : list (LinearDecisionIntMP.expr' * LinearDecisionIntMP.expr')) (b : Z) : Prop :=
match ctx with | [] => True | cons eq t => eq_bound' eq b ∧ ctx_bound' t b end.
Admit Obligations.
Axiom max_var' : LinearDecisionIntMP.expr' -> Z.
Axiom max_var''def : forall  (e : LinearDecisionIntMP.expr') (fact0 : LinearDecisionIntMP.valid_expr' e), match e with | LinearDecisionIntMP.Var i => max_var' e = i | LinearDecisionIntMP.Coeff _ => max_var' e = 0%Z | LinearDecisionIntMP.Sum e1 e2 => max_var' e = Z.max (max_var' e1) (max_var' e2) | LinearDecisionIntMP.Diff e1 e2 => max_var' e = Z.max (max_var' e1) (max_var' e2) | LinearDecisionIntMP.ProdL e1 _ => max_var' e = max_var' e1 | LinearDecisionIntMP.ProdR _ e1 => max_var' e = max_var' e1 end.
Axiom max_var''spec'0 : forall  (e : LinearDecisionIntMP.expr') (fact0 : LinearDecisionIntMP.valid_expr' e), 0%Z ≤ max_var' e.
Axiom max_var''spec : forall  (e : LinearDecisionIntMP.expr') (fact0 : LinearDecisionIntMP.valid_expr' e), expr_bound' e (max_var' e).
Axiom max_var_e' : LinearDecisionIntMP.expr' * LinearDecisionIntMP.expr' -> Z.
Axiom max_var_e''def : forall  (e : LinearDecisionIntMP.expr' * LinearDecisionIntMP.expr') (fact0 : LinearDecisionIntMP.valid_eq' e), match e with | (e1, e2) => max_var_e' e = Z.max (max_var' e1) (max_var' e2) end.
Axiom max_var_e''spec'0 : forall  (e : LinearDecisionIntMP.expr' * LinearDecisionIntMP.expr') (fact0 : LinearDecisionIntMP.valid_eq' e), 0%Z ≤ max_var_e' e.
Axiom max_var_e''spec : forall  (e : LinearDecisionIntMP.expr' * LinearDecisionIntMP.expr') (fact0 : LinearDecisionIntMP.valid_eq' e), eq_bound' e (max_var_e' e).
Axiom max_var_ctx' : list (LinearDecisionIntMP.expr' * LinearDecisionIntMP.expr') -> Z.
Axiom max_var_ctx''def : forall  (l : list (LinearDecisionIntMP.expr' * LinearDecisionIntMP.expr')) (fact0 : LinearDecisionIntMP.valid_ctx' l), match l with | [] => max_var_ctx' l = 0%Z | cons e t => max_var_ctx' l = Z.max (max_var_e' e) (max_var_ctx' t) end.
Axiom max_var_ctx''spec'0 : forall  (l : list (LinearDecisionIntMP.expr' * LinearDecisionIntMP.expr')) (fact0 : LinearDecisionIntMP.valid_ctx' l), 0%Z ≤ max_var_ctx' l.
Axiom max_var_ctx''spec : forall  (l : list (LinearDecisionIntMP.expr' * LinearDecisionIntMP.expr')) (fact0 : LinearDecisionIntMP.valid_ctx' l), ctx_bound' l (max_var_ctx' l).
Program Fixpoint ctx_impl_ctx' (c1 : list (LinearDecisionIntMP.expr' * LinearDecisionIntMP.expr')) (c2 : list (LinearDecisionIntMP.expr' * LinearDecisionIntMP.expr')) : Prop :=
match c2 with | [] => True | cons eq t => ctx_impl_ctx' c1 t ∧ (∀(y : Z -> Z) (z : Z -> Z), y = z -> LinearDecisionIntMP.interp_ctx' c1 eq y z = true) end.
Admit Obligations.
Program Fixpoint ctx_holds' (c : list (LinearDecisionIntMP.expr' * LinearDecisionIntMP.expr')) (y : Z -> Z) (z : Z -> Z) : Prop :=
match c with | [] => True | cons h t => LinearDecisionIntMP.interp_eq' h y z = true ∧ ctx_holds' t y z end.
Admit Obligations.
Definition is_eq_tbl (a : list (option MP64Coeffs.exp)) (l : list (LinearDecisionIntMP.expr' * LinearDecisionIntMP.expr')) := ∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length a) -> (match nth (Z.to_nat i) a inhabitant with | None => True | Some e => (∀(y : Z -> Z) (z : Z -> Z), y = z -> ctx_holds' l y z -> interp_exp (MP64Coeffs.Var i) z = interp_exp e z) end).
Axiom fc : forall {α : Type} `{Inhabited α}, list α -> α -> Z -> bool.
Axiom fc'def : forall  {α : Type} `{Inhabited α} (a : list α) (v : α) (i : Z), (fc a v i = true) = (nth (Z.to_nat i) a inhabitant = v).
