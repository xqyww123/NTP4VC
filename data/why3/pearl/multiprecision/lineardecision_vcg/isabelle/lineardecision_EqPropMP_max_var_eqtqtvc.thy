theory lineardecision_EqPropMP_max_var_eqtqtvc
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
consts max_var' :: "lineardecision_LinearDecisionIntMP.expr' \<Rightarrow> int"
axiomatization where max_var'_def:   "case e of lineardecision_LinearDecisionIntMP.Var i \<Rightarrow> max_var' e = i | lineardecision_LinearDecisionIntMP.Coeff _ \<Rightarrow> max_var' e = (0 :: int) | lineardecision_LinearDecisionIntMP.Sum e1 e2 \<Rightarrow> max_var' e = max (max_var' e1) (max_var' e2) | lineardecision_LinearDecisionIntMP.Diff e1 e2 \<Rightarrow> max_var' e = max (max_var' e1) (max_var' e2) | lineardecision_LinearDecisionIntMP.ProdL e1 _ \<Rightarrow> max_var' e = max_var' e1 | lineardecision_LinearDecisionIntMP.ProdR _ e1 \<Rightarrow> max_var' e = max_var' e1"
 if "lineardecision_LinearDecisionIntMP.valid_expr' e"
  for e :: "lineardecision_LinearDecisionIntMP.expr'"
axiomatization where max_var''spec'0:   "(0 :: int) \<le> max_var' e"
 if "lineardecision_LinearDecisionIntMP.valid_expr' e"
  for e :: "lineardecision_LinearDecisionIntMP.expr'"
axiomatization where max_var''spec:   "expr_bound' e (max_var' e)"
 if "lineardecision_LinearDecisionIntMP.valid_expr' e"
  for e :: "lineardecision_LinearDecisionIntMP.expr'"
theorem max_var_e''vc:
  fixes e1 :: "lineardecision_LinearDecisionIntMP.expr'"
  fixes e2 :: "lineardecision_LinearDecisionIntMP.expr'"
  shows "let e :: lineardecision_LinearDecisionIntMP.expr' \<times> lineardecision_LinearDecisionIntMP.expr' = (e1, e2) in lineardecision_LinearDecisionIntMP.valid_eq' e \<longrightarrow> (lineardecision_LinearDecisionIntMP.valid_expr' e2 \<and> (let o1 :: int = max_var' e2 in (0 :: int) \<le> o1 \<and> expr_bound' e2 o1 \<longrightarrow> lineardecision_LinearDecisionIntMP.valid_expr' e1)) \<and> (\<forall>(result :: int). (let o1 :: int = max_var' e2 in ((0 :: int) \<le> o1 \<and> expr_bound' e2 o1) \<and> (let o2 :: int = max_var' e1 in ((0 :: int) \<le> o2 \<and> expr_bound' e1 o2) \<and> result = max o2 o1)) \<longrightarrow> (0 :: int) \<le> result \<and> eq_bound' e result)"
  sorry
end
