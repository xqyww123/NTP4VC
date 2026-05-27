theory lineardecision_EqPropMP_ctx_bound_wqtqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "mach.matrix_Matrix63" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs" "pearl_multiprecision_lib.lineardecision_MP64Coeffs" "pearl_multiprecision_lib.lineardecision_LinearDecisionRationalMP" "pearl_multiprecision_lib.lineardecision_LinearDecisionIntMP"
begin
fun expr_bound' :: "lineardecision_LinearDecisionIntMP.expr' \<Rightarrow> int \<Rightarrow> _"
  where "expr_bound' (lineardecision_LinearDecisionIntMP.Sum e1 e2) b = (expr_bound' e1 b \<and> expr_bound' e2 b)" for e1 e2 b
      | "expr_bound' (lineardecision_LinearDecisionIntMP.Diff e1 e2) b = (expr_bound' e1 b \<and> expr_bound' e2 b)" for e1 e2 b
      | "expr_bound' (lineardecision_LinearDecisionIntMP.ProdL e1 x) b = expr_bound' e1 b" for e1 x b
      | "expr_bound' (lineardecision_LinearDecisionIntMP.ProdR x e1) b = expr_bound' e1 b" for x e1 b
      | "expr_bound' (lineardecision_LinearDecisionIntMP.Var n) b = ((0 :: int) \<le> n \<and> n \<le> b)" for n b
      | "expr_bound' (lineardecision_LinearDecisionIntMP.Coeff x) b = True" for x b
definition eq_bound' :: "lineardecision_LinearDecisionIntMP.expr' \<times> lineardecision_LinearDecisionIntMP.expr' \<Rightarrow> int \<Rightarrow> _"
  where "eq_bound' eq b \<longleftrightarrow> (case eq of (e1, e2) \<Rightarrow> expr_bound' e1 b \<and> expr_bound' e2 b)" for eq b
fun ctx_bound' :: "(lineardecision_LinearDecisionIntMP.expr' \<times> lineardecision_LinearDecisionIntMP.expr') list \<Rightarrow> int \<Rightarrow> _"
  where "ctx_bound' (Nil :: (lineardecision_LinearDecisionIntMP.expr' \<times> lineardecision_LinearDecisionIntMP.expr') list) b = True" for b
      | "ctx_bound' (Cons eq t) b = (eq_bound' eq b \<and> ctx_bound' t b)" for eq t b
theorem ctx_bound_w''vc:
  fixes l :: "(lineardecision_LinearDecisionIntMP.expr' \<times> lineardecision_LinearDecisionIntMP.expr') list"
  fixes b1 :: "int"
  fixes b2 :: "int"
  assumes fact0: "ctx_bound' l b1"
  assumes fact1: "b1 \<le> b2"
  shows "ctx_bound' l b2"
  sorry
end
