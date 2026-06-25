theory lineardecision_LinearDecisionIntMP_mqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "mach.matrix_Matrix63" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs" "pearl_multiprecision_lib.lineardecision_MP64Coeffs" "pearl_multiprecision_lib.lineardecision_LinearDecisionRationalMP"
begin
datatype  t = I "int" | E "exp" | R
definition mpinterp :: "t \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int"
  where "mpinterp t1 y = (case t1 of I n \<Rightarrow> n | E e \<Rightarrow> ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i interp_exp e y | R \<Rightarrow> (18446744073709551615 :: int) + (1 :: int))" for t1 y
axiomatization where mpeq'spec:   "True"
axiomatization where sub_def:   "a1 - a2 = a1 + -a2"
  for a1 :: "int"
  and a2 :: "int"
typedecl  vars
axiomatization where zero_def:   "mpinterp (I (0 :: int)) y = (0 :: int)"
  for y :: "int \<Rightarrow> int"
axiomatization where one_def:   "mpinterp (I (1 :: int)) y = (1 :: int)"
  for y :: "int \<Rightarrow> int"
typedecl  vars1
datatype  expr = Term "t" "int" | Add "expr" "expr" | Cst "t"
fun valid_expr :: "expr \<Rightarrow> _"
  where "valid_expr (Term x i) = ((0 :: int) \<le> i)" for x i
      | "valid_expr (Cst x) = True" for x
      | "valid_expr (Add e1 e2) = (valid_expr e1 \<and> valid_expr e2)" for e1 e2
fun expr_bound :: "expr \<Rightarrow> int \<Rightarrow> _"
  where "expr_bound (Term x i) b = ((0 :: int) \<le> i \<and> i \<le> b)" for x i b
      | "expr_bound (Cst x) b = True" for x b
      | "expr_bound (Add e1 e2) b = (expr_bound e1 b \<and> expr_bound e2 b)" for e1 e2 b
fun interp :: "expr \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int"
  where "interp (Term c v) y z = mpinterp c z * y v" for c v y z
      | "interp (Add e1 e2) y z = interp e1 y z + interp e2 y z" for e1 e2 y z
      | "interp (Cst c) y z = mpinterp c z" for c y z
typedecl  equality
typedecl  "context"
definition valid_eq :: "expr \<times> expr \<Rightarrow> _"
  where "valid_eq eq \<longleftrightarrow> (case eq of (e1, e2) \<Rightarrow> valid_expr e1 \<and> valid_expr e2)" for eq
definition eq_bound :: "expr \<times> expr \<Rightarrow> int \<Rightarrow> _"
  where "eq_bound eq b \<longleftrightarrow> (case eq of (e1, e2) \<Rightarrow> expr_bound e1 b \<and> expr_bound e2 b)" for eq b
fun valid_ctx :: "(expr \<times> expr) list \<Rightarrow> _"
  where "valid_ctx (Nil :: (expr \<times> expr) list) = True"
      | "valid_ctx (Cons eq t1) = (valid_eq eq \<and> valid_ctx t1)" for eq t1
fun ctx_bound :: "(expr \<times> expr) list \<Rightarrow> int \<Rightarrow> _"
  where "ctx_bound (Nil :: (expr \<times> expr) list) b = True" for b
      | "ctx_bound (Cons eq t1) b = (eq_bound eq b \<and> ctx_bound t1 b)" for eq t1 b
definition interp_eq :: "expr \<times> expr \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> bool"
  where "interp_eq g y z = (if case g of (g1, g2) \<Rightarrow> interp g1 y z = interp g2 y z then True else False)" for g y z
fun interp_ctx :: "(expr \<times> expr) list \<Rightarrow> expr \<times> expr \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> bool"
  where "interp_ctx l g y z = (if case l of Nil \<Rightarrow> interp_eq g y z = True | Cons h t1 \<Rightarrow> interp_eq h y z = True \<longrightarrow> interp_ctx t1 g y z = True then True else False)" for l g y z
consts infix_eqeq :: "t array63 \<Rightarrow> t array63 \<Rightarrow> bool"
axiomatization where infix_eqeq'spec'0:   "array63_length a = array63_length b"
 if "infix_eqeq a b"
  for a :: "t array63"
  and b :: "t array63"
axiomatization where infix_eqeq'spec'1:   "\<forall>(i :: int). \<not>((0 :: int) \<le> i \<and> i < sint (array63_length a))"
 if "infix_eqeq a b"
  for a :: "t array63"
  and b :: "t array63"
consts max_var :: "expr \<Rightarrow> int"
axiomatization where max_var_def:   "case e of Term _ i \<Rightarrow> max_var e = i | Cst _ \<Rightarrow> max_var e = (0 :: int) | Add e1 e2 \<Rightarrow> max_var e = max (max_var e1) (max_var e2)"
 if "valid_expr e"
  for e :: "expr"
axiomatization where max_var'spec'0:   "(0 :: int) \<le> max_var e"
 if "valid_expr e"
  for e :: "expr"
axiomatization where max_var'spec:   "expr_bound e (max_var e)"
 if "valid_expr e"
  for e :: "expr"
consts max_var_e :: "expr \<times> expr \<Rightarrow> int"
axiomatization where max_var_e_def:   "case e of (e1, e2) \<Rightarrow> max_var_e e = max (max_var e1) (max_var e2)"
 if "valid_eq e"
  for e :: "expr \<times> expr"
axiomatization where max_var_e'spec'0:   "(0 :: int) \<le> max_var_e e"
 if "valid_eq e"
  for e :: "expr \<times> expr"
axiomatization where max_var_e'spec:   "eq_bound e (max_var_e e)"
 if "valid_eq e"
  for e :: "expr \<times> expr"
consts max_var_ctx :: "(expr \<times> expr) list \<Rightarrow> int"
axiomatization where max_var_ctx_def:   "case l of Nil \<Rightarrow> max_var_ctx l = (0 :: int) | Cons e t1 \<Rightarrow> max_var_ctx l = max (max_var_e e) (max_var_ctx t1)"
 if "valid_ctx l"
  for l :: "(expr \<times> expr) list"
axiomatization where max_var_ctx'spec'0:   "(0 :: int) \<le> max_var_ctx l"
 if "valid_ctx l"
  for l :: "(expr \<times> expr) list"
axiomatization where max_var_ctx'spec:   "ctx_bound l (max_var_ctx l)"
 if "valid_ctx l"
  for l :: "(expr \<times> expr) list"
definition atom :: "expr \<Rightarrow> _"
  where "atom e \<longleftrightarrow> (case e of Add _ _ \<Rightarrow> False | _ \<Rightarrow> True)" for e
consts to_list :: "'a array63 \<Rightarrow> 63 word \<Rightarrow> 63 word \<Rightarrow> 'a list"
datatype  expr' = Sum "expr'" "expr'" | ProdL "expr'" "cprod" | ProdR "cprod" "expr'" | Diff "expr'" "expr'" | Var "int" | Coeff "t"
     and  cprod = C "t" | Times "cprod" "cprod"
fun interp_c :: "cprod \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int"
  where "interp_c (C c) y z = mpinterp c z" for c y z
      | "interp_c (Times e1 e2) y z = interp_c e1 y z * interp_c e2 y z" for e1 e2 y z
fun interp' :: "expr' \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int"
  where "interp' (Sum e1 e2) y z = interp' e1 y z + interp' e2 y z" for e1 e2 y z
      | "interp' (ProdL e1 c) y z = interp' e1 y z * interp_c c y z" for e1 c y z
      | "interp' (ProdR c e1) y z = interp_c c y z * interp' e1 y z" for c e1 y z
      | "interp' (Diff e1 e2) y z = interp' e1 y z - interp' e2 y z" for e1 e2 y z
      | "interp' (Var n) y z = y n" for n y z
      | "interp' (Coeff c) y z = mpinterp c z" for c y z
typedecl  equality'
typedecl  context'
definition interp_eq' :: "expr' \<times> expr' \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> bool"
  where "interp_eq' g y z = (if case g of (g1, g2) \<Rightarrow> interp' g1 y z = interp' g2 y z then True else False)" for g y z
fun interp_ctx' :: "(expr' \<times> expr') list \<Rightarrow> expr' \<times> expr' \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> bool"
  where "interp_ctx' l g y z = (if case l of Nil \<Rightarrow> interp_eq' g y z = True | Cons h t1 \<Rightarrow> interp_eq' h y z = True \<longrightarrow> interp_ctx' t1 g y z = True then True else False)" for l g y z
fun valid_expr' :: "expr' \<Rightarrow> _"
  where "valid_expr' (Var i) = ((0 :: int) \<le> i)" for i
      | "valid_expr' (Sum e1 e2) = (valid_expr' e1 \<and> valid_expr' e2)" for e1 e2
      | "valid_expr' (Diff e1 e2) = (valid_expr' e1 \<and> valid_expr' e2)" for e1 e2
      | "valid_expr' (Coeff x) = True" for x
      | "valid_expr' (ProdL e1 x) = valid_expr' e1" for e1 x
      | "valid_expr' (ProdR x e1) = valid_expr' e1" for x e1
definition valid_eq' :: "expr' \<times> expr' \<Rightarrow> _"
  where "valid_eq' eq \<longleftrightarrow> (case eq of (e1, e2) \<Rightarrow> valid_expr' e1 \<and> valid_expr' e2)" for eq
fun valid_ctx' :: "(expr' \<times> expr') list \<Rightarrow> _"
  where "valid_ctx' (Nil :: (expr' \<times> expr') list) = True"
      | "valid_ctx' (Cons eq t1) = (valid_eq' eq \<and> valid_ctx' t1)" for eq t1
definition pos_exp :: "t \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> _"
  where "pos_exp t1 y \<longleftrightarrow> (case t1 of E e \<Rightarrow> (0 :: int) \<le> interp_exp e y | I _ \<Rightarrow> True | R \<Rightarrow> True)" for t1 y
fun pos_cprod :: "cprod \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> _"
  where "pos_cprod (C c) y = pos_exp c y" for c y
      | "pos_cprod (Times c1 c2) y = (pos_cprod c1 y \<and> pos_cprod c2 y)" for c1 c2 y
fun pos_expr' :: "expr' \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> _"
  where "pos_expr' (Coeff c) y = pos_exp c y" for c y
      | "pos_expr' (Var x) y = True" for x y
      | "pos_expr' (Sum e1 e2) y = (pos_expr' e1 y \<and> pos_expr' e2 y)" for e1 e2 y
      | "pos_expr' (Diff e1 e2) y = (pos_expr' e1 y \<and> pos_expr' e2 y)" for e1 e2 y
      | "pos_expr' (ProdL e1 c) y = (pos_expr' e1 y \<and> pos_cprod c y)" for e1 c y
      | "pos_expr' (ProdR c e1) y = (pos_expr' e1 y \<and> pos_cprod c y)" for c e1 y
definition pos_eq' :: "expr' \<times> expr' \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> _"
  where "pos_eq' eq y \<longleftrightarrow> (case eq of (e1, e2) \<Rightarrow> pos_expr' e1 y \<and> pos_expr' e2 y)" for eq y
fun pos_ctx' :: "(expr' \<times> expr') list \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> _"
  where "pos_ctx' (Nil :: (expr' \<times> expr') list) y = True" for y
      | "pos_ctx' (Cons h t1) y = (pos_eq' h y \<and> pos_ctx' t1 y)" for h t1 y
theorem m'vc:
  fixes t1 :: "t"
  shows "case t1 of I n \<Rightarrow> True | E e \<Rightarrow> True | R \<Rightarrow> True"
  and "\<forall>(result :: int) (result1 :: int) (result2 :: exp). (case t1 of I n \<Rightarrow> (result = n \<and> result1 = (1 :: int)) \<and> result2 = Lit (0 :: int) | E e \<Rightarrow> (result = (1 :: int) \<and> result1 = (1 :: int)) \<and> result2 = e | R \<Rightarrow> (result = (1 :: int) \<and> result1 = (1 :: int)) \<and> result2 = Lit (1 :: int)) \<longrightarrow> (\<forall>(y :: int \<Rightarrow> int). pos_exp t1 y \<longrightarrow> minterp ((result, result1), result2) y = real_of_int (mpinterp t1 y))"
  sorry
end
