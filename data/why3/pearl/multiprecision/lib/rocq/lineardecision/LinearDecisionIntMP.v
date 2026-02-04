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
Require Import multiprecision.lineardecision.LinearDecisionRationalMP.
Open Scope Z_scope.
Inductive t :=
  | I : Z -> t
  | E : MP64Coeffs.exp -> t
  | R : t.
Axiom t_inhabited : Inhabited t.
Global Existing Instance t_inhabited.
Axiom t_countable : Countable t.
Global Existing Instance t_countable.
Definition mpinterp (t1 : t) (y : Z -> Z) : Z := match t1 with | I n => n | E e => Z.pow (18446744073709551615%Z + 1%Z) (interp_exp e y) | R => 18446744073709551615%Z + 1%Z end.
Axiom mpeq'spec : True.
Axiom sub_def : forall  (a1 : Z) (a2 : Z), a1 - a2 = a1 + - a2.
Axiom vars : Type.
Axiom vars_inhabited : Inhabited vars.
Global Existing Instance vars_inhabited.
Axiom vars_countable : Countable vars.
Global Existing Instance vars_countable.
Axiom zero_def : forall  (y : Z -> Z), mpinterp (I 0%Z) y = 0%Z.
Axiom one_def : forall  (y : Z -> Z), mpinterp (I 1%Z) y = 1%Z.
Axiom vars1 : Type.
Axiom vars1_inhabited : Inhabited vars1.
Global Existing Instance vars1_inhabited.
Axiom vars1_countable : Countable vars1.
Global Existing Instance vars1_countable.
Inductive expr :=
  | Term : t -> Z -> expr
  | Add : expr -> expr -> expr
  | Cst : t -> expr.
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
Program Fixpoint interp (e : expr) (y : Z -> Z) (z : Z -> Z) : Z :=
match e with | Term c v => mpinterp c z * y v | Add e1 e2 => interp e1 y z + interp e2 y z | Cst c => mpinterp c z end.
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
match ctx with | [] => True | cons eq t1 => valid_eq eq ∧ valid_ctx t1 end.
Admit Obligations.
Program Fixpoint ctx_bound (ctx : list (expr * expr)) (b : Z) : Prop :=
match ctx with | [] => True | cons eq t1 => eq_bound eq b ∧ ctx_bound t1 b end.
Admit Obligations.
Definition interp_eq (g : expr * expr) (y : Z -> Z) (z : Z -> Z) : bool := if decide (match g with | (g1, g2) => interp g1 y z = interp g2 y z end) then true else false.
Program Fixpoint interp_ctx (l : list (expr * expr)) (g : expr * expr) (y : Z -> Z) (z : Z -> Z) : bool :=
if decide (match l with | [] => interp_eq g y z = true | cons h t1 => interp_eq h y z = true -> interp_ctx t1 g y z = true end) then true else false.
Admit Obligations.
Axiom infix_eqeq : array63 t -> array63 t -> Prop.
Axiom infix_eqeq'spec : forall  (a : array63 t) (b : array63 t) (fact0 : infix_eqeq a b), array63_length a = array63_length b ∧ (∀(i : Z), ¬ (0%Z ≤ i ∧ i < bv_signed (array63_length a))).
Axiom max_var : expr -> Z.
Axiom max_var'def : forall  (e : expr) (fact0 : valid_expr e), match e with | Term _ i => max_var e = i | Cst _ => max_var e = 0%Z | Add e1 e2 => max_var e = Z.max (max_var e1) (max_var e2) end.
Axiom max_var'spec'0 : forall  (e : expr) (fact0 : valid_expr e), 0%Z ≤ max_var e.
Axiom max_var'spec : forall  (e : expr) (fact0 : valid_expr e), expr_bound e (max_var e).
Axiom max_var_e : expr * expr -> Z.
Axiom max_var_e'def : forall  (e : expr * expr) (fact0 : valid_eq e), match e with | (e1, e2) => max_var_e e = Z.max (max_var e1) (max_var e2) end.
Axiom max_var_e'spec'0 : forall  (e : expr * expr) (fact0 : valid_eq e), 0%Z ≤ max_var_e e.
Axiom max_var_e'spec : forall  (e : expr * expr) (fact0 : valid_eq e), eq_bound e (max_var_e e).
Axiom max_var_ctx : list (expr * expr) -> Z.
Axiom max_var_ctx'def : forall  (l : list (expr * expr)) (fact0 : valid_ctx l), match l with | [] => max_var_ctx l = 0%Z | cons e t1 => max_var_ctx l = Z.max (max_var_e e) (max_var_ctx t1) end.
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
  | Coeff : t -> expr'
with cprod :=
  | C : t -> cprod
  | Times : cprod -> cprod -> cprod.
Axiom expr'_inhabited : Inhabited expr'.
Global Existing Instance expr'_inhabited.
Axiom expr'_countable : Countable expr'.
Global Existing Instance expr'_countable.
Axiom cprod_inhabited : Inhabited cprod.
Global Existing Instance cprod_inhabited.
Axiom cprod_countable : Countable cprod.
Global Existing Instance cprod_countable.
Program Fixpoint interp_c (e : cprod) (y : Z -> Z) (z : Z -> Z) : Z :=
match e with | C c => mpinterp c z | Times e1 e2 => interp_c e1 y z * interp_c e2 y z end.
Admit Obligations.
Program Fixpoint interp' (e : expr') (y : Z -> Z) (z : Z -> Z) : Z :=
match e with | Sum e1 e2 => interp' e1 y z + interp' e2 y z | ProdL e1 c => interp' e1 y z * interp_c c y z | ProdR c e1 => interp_c c y z * interp' e1 y z | Diff e1 e2 => interp' e1 y z - interp' e2 y z | Var n => y n | Coeff c => mpinterp c z end.
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
Definition interp_eq' (g : expr' * expr') (y : Z -> Z) (z : Z -> Z) : bool := if decide (match g with | (g1, g2) => interp' g1 y z = interp' g2 y z end) then true else false.
Program Fixpoint interp_ctx' (l : list (expr' * expr')) (g : expr' * expr') (y : Z -> Z) (z : Z -> Z) : bool :=
if decide (match l with | [] => interp_eq' g y z = true | cons h t1 => interp_eq' h y z = true -> interp_ctx' t1 g y z = true end) then true else false.
Admit Obligations.
Program Fixpoint valid_expr' (e : expr') : Prop :=
match e with | Var i => 0%Z ≤ i | Sum e1 e2 => valid_expr' e1 ∧ valid_expr' e2 | Diff e1 e2 => valid_expr' e1 ∧ valid_expr' e2 | Coeff _ => True | ProdL e1 _ => valid_expr' e1 | ProdR _ e1 => valid_expr' e1 end.
Admit Obligations.
Definition valid_eq' (eq : expr' * expr') := match eq with | (e1, e2) => valid_expr' e1 ∧ valid_expr' e2 end.
Program Fixpoint valid_ctx' (ctx : list (expr' * expr')) : Prop :=
match ctx with | [] => True | cons eq t1 => valid_eq' eq ∧ valid_ctx' t1 end.
Admit Obligations.
Definition pos_exp (t1 : t) (y : Z -> Z) := match t1 with | E e => 0%Z ≤ interp_exp e y | I _ => True | R => True end.
Program Fixpoint pos_cprod (e : cprod) (y : Z -> Z) : Prop :=
match e with | C c => pos_exp c y | Times c1 c2 => pos_cprod c1 y ∧ pos_cprod c2 y end.
Admit Obligations.
Program Fixpoint pos_expr' (e : expr') (y : Z -> Z) : Prop :=
match e with | Coeff c => pos_exp c y | Var _ => True | Sum e1 e2 => pos_expr' e1 y ∧ pos_expr' e2 y | Diff e1 e2 => pos_expr' e1 y ∧ pos_expr' e2 y | ProdL e1 c => pos_expr' e1 y ∧ pos_cprod c y | ProdR c e1 => pos_expr' e1 y ∧ pos_cprod c y end.
Admit Obligations.
Definition pos_eq' (eq : expr' * expr') (y : Z -> Z) := match eq with | (e1, e2) => pos_expr' e1 y ∧ pos_expr' e2 y end.
Program Fixpoint pos_ctx' (l : list (expr' * expr')) (y : Z -> Z) : Prop :=
match l with | [] => True | cons h t1 => pos_eq' h y ∧ pos_ctx' t1 y end.
Admit Obligations.
Definition m (t1 : t) : Z * Z * MP64Coeffs.exp := match t1 with | I n => ((n, 1%Z), Lit 0%Z) | E e => ((1%Z, 1%Z), e) | R => ((1%Z, 1%Z), Lit 1%Z) end.
Axiom m'spec : forall  (t1 : t) (y : Z -> Z) (fact0 : pos_exp t1 y), minterp (m t1) y = Rdefinitions.IZR (mpinterp t1 y).
Axiom m_y : (Z -> Z) -> Z -> Rdefinitions.R.
Axiom m_y'def : forall  (y : Z -> Z) (i : Z), m_y y i = Rdefinitions.IZR (y i).
Axiom m_y'spec : forall  (y : Z -> Z) (i : Z), m_y y i = Rdefinitions.IZR (y i).
Program Fixpoint m_cprod (e : cprod) : LinearDecisionRationalMP.cprod :=
match e with | C c => LinearDecisionRationalMP.C (m c) | Times c1 c2 => LinearDecisionRationalMP.Times (m_cprod c1) (m_cprod c2) end.
Admit Obligations.
Axiom m_cprod'spec : forall  (e : cprod) (z : Z -> Z) (y : Z -> Z) (fact0 : pos_cprod e z), LinearDecisionRationalMP.interp_c (m_cprod e) (m_y y) z = Rdefinitions.IZR (interp_c e y z).
Program Fixpoint m_expr (e : expr') : LinearDecisionRationalMP.expr' :=
match e with | Var i => LinearDecisionRationalMP.Var i | Coeff c => LinearDecisionRationalMP.Coeff (m c) | Sum e1 e2 => LinearDecisionRationalMP.Sum (m_expr e1) (m_expr e2) | Diff e1 e2 => LinearDecisionRationalMP.Diff (m_expr e1) (m_expr e2) | ProdL e1 c => LinearDecisionRationalMP.ProdL (m_expr e1) (m_cprod c) | ProdR c e1 => LinearDecisionRationalMP.ProdR (m_cprod c) (m_expr e1) end.
Admit Obligations.
Axiom m_expr'spec'0 : forall  (e : expr') (z : Z -> Z) (y : Z -> Z) (fact0 : pos_expr' e z), LinearDecisionRationalMP.interp' (m_expr e) (m_y y) z = Rdefinitions.IZR (interp' e y z).
Axiom m_expr'spec : forall  (e : expr') (fact0 : valid_expr' e), LinearDecisionRationalMP.valid_expr' (m_expr e).
Definition m_eq (eq : expr' * expr') : LinearDecisionRationalMP.expr' * LinearDecisionRationalMP.expr' := match eq with | (e1, e2) => (m_expr e1, m_expr e2) end.
Axiom m_eq'spec'0 : forall  (eq : expr' * expr') (z : Z -> Z) (y : Z -> Z) (fact0 : pos_eq' eq z), (LinearDecisionRationalMP.interp_eq' (m_eq eq) (m_y y) z = true) = (interp_eq' eq y z = true).
Axiom m_eq'spec : forall  (eq : expr' * expr') (fact0 : valid_eq' eq), LinearDecisionRationalMP.valid_eq' (m_eq eq).
Program Fixpoint m_ctx (ctx : list (expr' * expr')) : list (LinearDecisionRationalMP.expr' * LinearDecisionRationalMP.expr') :=
match ctx with | [] => ([] : list (LinearDecisionRationalMP.expr' * LinearDecisionRationalMP.expr')) | cons h t1 => cons (m_eq h) (m_ctx t1) end.
Admit Obligations.
Axiom m_ctx'spec'1 : forall  (ctx : list (expr' * expr')) (z : Z -> Z) (g : expr' * expr') (y : Z -> Z) (fact0 : pos_ctx' ctx z) (fact1 : pos_eq' g z), (LinearDecisionRationalMP.interp_ctx' (m_ctx ctx) (m_eq g) (m_y y) z = true) = (interp_ctx' ctx g y z = true).
Axiom m_ctx'spec'0 : forall  (ctx : list (expr' * expr')), length (m_ctx ctx) = length ctx.
Axiom m_ctx'spec : forall  (ctx : list (expr' * expr')) (fact0 : valid_ctx' ctx), LinearDecisionRationalMP.valid_ctx' (m_ctx ctx).
