theory lineardecision_EqPropMP_interp_ctx_implqtqtvc
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
consts max_var_e' :: "lineardecision_LinearDecisionIntMP.expr' \<times> lineardecision_LinearDecisionIntMP.expr' \<Rightarrow> int"
axiomatization where max_var_e'_def:   "case e of (e1, e2) \<Rightarrow> max_var_e' e = max (max_var' e1) (max_var' e2)"
 if "lineardecision_LinearDecisionIntMP.valid_eq' e"
  for e :: "lineardecision_LinearDecisionIntMP.expr' \<times> lineardecision_LinearDecisionIntMP.expr'"
axiomatization where max_var_e''spec'0:   "(0 :: int) \<le> max_var_e' e"
 if "lineardecision_LinearDecisionIntMP.valid_eq' e"
  for e :: "lineardecision_LinearDecisionIntMP.expr' \<times> lineardecision_LinearDecisionIntMP.expr'"
axiomatization where max_var_e''spec:   "eq_bound' e (max_var_e' e)"
 if "lineardecision_LinearDecisionIntMP.valid_eq' e"
  for e :: "lineardecision_LinearDecisionIntMP.expr' \<times> lineardecision_LinearDecisionIntMP.expr'"
consts max_var_ctx' :: "(lineardecision_LinearDecisionIntMP.expr' \<times> lineardecision_LinearDecisionIntMP.expr') list \<Rightarrow> int"
axiomatization where max_var_ctx'_def:   "case l of Nil \<Rightarrow> max_var_ctx' l = (0 :: int) | Cons e t \<Rightarrow> max_var_ctx' l = max (max_var_e' e) (max_var_ctx' t)"
 if "lineardecision_LinearDecisionIntMP.valid_ctx' l"
  for l :: "(lineardecision_LinearDecisionIntMP.expr' \<times> lineardecision_LinearDecisionIntMP.expr') list"
axiomatization where max_var_ctx''spec'0:   "(0 :: int) \<le> max_var_ctx' l"
 if "lineardecision_LinearDecisionIntMP.valid_ctx' l"
  for l :: "(lineardecision_LinearDecisionIntMP.expr' \<times> lineardecision_LinearDecisionIntMP.expr') list"
axiomatization where max_var_ctx''spec:   "ctx_bound' l (max_var_ctx' l)"
 if "lineardecision_LinearDecisionIntMP.valid_ctx' l"
  for l :: "(lineardecision_LinearDecisionIntMP.expr' \<times> lineardecision_LinearDecisionIntMP.expr') list"
fun ctx_impl_ctx' :: "(lineardecision_LinearDecisionIntMP.expr' \<times> lineardecision_LinearDecisionIntMP.expr') list \<Rightarrow> (lineardecision_LinearDecisionIntMP.expr' \<times> lineardecision_LinearDecisionIntMP.expr') list \<Rightarrow> _"
  where "ctx_impl_ctx' c1 (Nil :: (lineardecision_LinearDecisionIntMP.expr' \<times> lineardecision_LinearDecisionIntMP.expr') list) = True" for c1
      | "ctx_impl_ctx' c1 (Cons eq t) = (ctx_impl_ctx' c1 t \<and> (\<forall>(y :: int \<Rightarrow> int) (z :: int \<Rightarrow> int). y = z \<longrightarrow> lineardecision_LinearDecisionIntMP.interp_ctx' c1 eq y z = True))" for c1 eq t
fun ctx_holds' :: "(lineardecision_LinearDecisionIntMP.expr' \<times> lineardecision_LinearDecisionIntMP.expr') list \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> _"
  where "ctx_holds' (Nil :: (lineardecision_LinearDecisionIntMP.expr' \<times> lineardecision_LinearDecisionIntMP.expr') list) y z = True" for y z
      | "ctx_holds' (Cons h t) y z = (lineardecision_LinearDecisionIntMP.interp_eq' h y z = True \<and> ctx_holds' t y z)" for h t y z
theorem interp_ctx_impl''vc:
  fixes g2 :: "lineardecision_LinearDecisionIntMP.expr'"
  fixes g21 :: "lineardecision_LinearDecisionIntMP.expr'"
  fixes g1 :: "lineardecision_LinearDecisionIntMP.expr'"
  fixes g11 :: "lineardecision_LinearDecisionIntMP.expr'"
  fixes ctx :: "(lineardecision_LinearDecisionIntMP.expr' \<times> lineardecision_LinearDecisionIntMP.expr') list"
  shows "let g22 :: lineardecision_LinearDecisionIntMP.expr' \<times> lineardecision_LinearDecisionIntMP.expr' = (g2, g21); g12 :: lineardecision_LinearDecisionIntMP.expr' \<times> lineardecision_LinearDecisionIntMP.expr' = (g1, g11) in (\<forall>(y :: int \<Rightarrow> int) (z :: int \<Rightarrow> int). lineardecision_LinearDecisionIntMP.interp_eq' g12 y z = True \<longrightarrow> lineardecision_LinearDecisionIntMP.interp_eq' g22 y z = True) \<longrightarrow> (\<forall>(y :: int \<Rightarrow> int) (z :: int \<Rightarrow> int). lineardecision_LinearDecisionIntMP.interp_ctx' ctx g12 y z = True \<longrightarrow> lineardecision_LinearDecisionIntMP.interp_ctx' ctx g22 y z = True)"
  sorry
end
