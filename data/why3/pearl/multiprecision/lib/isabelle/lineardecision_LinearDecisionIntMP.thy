theory lineardecision_LinearDecisionIntMP
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "mach.matrix_Matrix63" "Why3STD.debug_Debug" "../../lib/isabelle/lineardecision_RationalCoeffs" "../../lib/isabelle/lineardecision_MP64Coeffs" "../../lib/isabelle/lineardecision_LinearDecisionRationalMP"
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
axiomatization where max_var'def:   "case e of Term _ i \<Rightarrow> max_var e = i | Cst _ \<Rightarrow> max_var e = (0 :: int) | Add e1 e2 \<Rightarrow> max_var e = max (max_var e1) (max_var e2)"
 if "valid_expr e"
  for e :: "expr"
axiomatization where max_var'spec'0:   "(0 :: int) \<le> max_var e"
 if "valid_expr e"
  for e :: "expr"
axiomatization where max_var'spec:   "expr_bound e (max_var e)"
 if "valid_expr e"
  for e :: "expr"
consts max_var_e :: "expr \<times> expr \<Rightarrow> int"
axiomatization where max_var_e'def:   "case e of (e1, e2) \<Rightarrow> max_var_e e = max (max_var e1) (max_var e2)"
 if "valid_eq e"
  for e :: "expr \<times> expr"
axiomatization where max_var_e'spec'0:   "(0 :: int) \<le> max_var_e e"
 if "valid_eq e"
  for e :: "expr \<times> expr"
axiomatization where max_var_e'spec:   "eq_bound e (max_var_e e)"
 if "valid_eq e"
  for e :: "expr \<times> expr"
consts max_var_ctx :: "(expr \<times> expr) list \<Rightarrow> int"
axiomatization where max_var_ctx'def:   "case l of Nil \<Rightarrow> max_var_ctx l = (0 :: int) | Cons e t1 \<Rightarrow> max_var_ctx l = max (max_var_e e) (max_var_ctx t1)"
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
definition m :: "t \<Rightarrow> (int \<times> int) \<times> exp"
  where "m t1 = (case t1 of I n \<Rightarrow> ((n, 1 :: int), Lit (0 :: int)) | E e \<Rightarrow> ((1 :: int, 1 :: int), e) | R \<Rightarrow> ((1 :: int, 1 :: int), Lit (1 :: int)))" for t1
axiomatization where m'spec:   "minterp (m t1) y = real_of_int (mpinterp t1 y)"
 if "pos_exp t1 y"
  for t1 :: "t"
  and y :: "int \<Rightarrow> int"
consts m_y :: "(int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> real"
axiomatization where m_y'def:   "m_y y i = real_of_int (y i)"
  for y :: "int \<Rightarrow> int"
  and i :: "int"
axiomatization where m_y'spec:   "m_y y i = real_of_int (y i)"
  for y :: "int \<Rightarrow> int"
  and i :: "int"
fun m_cprod :: "cprod \<Rightarrow> lineardecision_LinearDecisionRationalMP.cprod"
  where "m_cprod (C c) = lineardecision_LinearDecisionRationalMP.C (m c)" for c
      | "m_cprod (Times c1 c2) = lineardecision_LinearDecisionRationalMP.Times (m_cprod c1) (m_cprod c2)" for c1 c2
axiomatization where m_cprod'spec:   "lineardecision_LinearDecisionRationalMP.interp_c (m_cprod e) (m_y y) z = real_of_int (interp_c e y z)"
 if "pos_cprod e z"
  for e :: "cprod"
  and z :: "int \<Rightarrow> int"
  and y :: "int \<Rightarrow> int"
fun m_expr :: "expr' \<Rightarrow> lineardecision_LinearDecisionRationalMP.expr'"
  where "m_expr (Var i) = lineardecision_LinearDecisionRationalMP.Var i" for i
      | "m_expr (Coeff c) = lineardecision_LinearDecisionRationalMP.Coeff (m c)" for c
      | "m_expr (Sum e1 e2) = lineardecision_LinearDecisionRationalMP.Sum (m_expr e1) (m_expr e2)" for e1 e2
      | "m_expr (Diff e1 e2) = lineardecision_LinearDecisionRationalMP.Diff (m_expr e1) (m_expr e2)" for e1 e2
      | "m_expr (ProdL e1 c) = lineardecision_LinearDecisionRationalMP.ProdL (m_expr e1) (m_cprod c)" for e1 c
      | "m_expr (ProdR c e1) = lineardecision_LinearDecisionRationalMP.ProdR (m_cprod c) (m_expr e1)" for c e1
axiomatization where m_expr'spec'0:   "lineardecision_LinearDecisionRationalMP.interp' (m_expr e) (m_y y) z = real_of_int (interp' e y z)"
 if "pos_expr' e z"
  for e :: "expr'"
  and z :: "int \<Rightarrow> int"
  and y :: "int \<Rightarrow> int"
axiomatization where m_expr'spec:   "lineardecision_LinearDecisionRationalMP.valid_expr' (m_expr e)"
 if "valid_expr' e"
  for e :: "expr'"
definition m_eq :: "expr' \<times> expr' \<Rightarrow> lineardecision_LinearDecisionRationalMP.expr' \<times> lineardecision_LinearDecisionRationalMP.expr'"
  where "m_eq eq = (case eq of (e1, e2) \<Rightarrow> (m_expr e1, m_expr e2))" for eq
axiomatization where m_eq'spec'0:   "lineardecision_LinearDecisionRationalMP.interp_eq' (m_eq eq) (m_y y) z = True \<longleftrightarrow> interp_eq' eq y z = True"
 if "pos_eq' eq z"
  for eq :: "expr' \<times> expr'"
  and z :: "int \<Rightarrow> int"
  and y :: "int \<Rightarrow> int"
axiomatization where m_eq'spec:   "lineardecision_LinearDecisionRationalMP.valid_eq' (m_eq eq)"
 if "valid_eq' eq"
  for eq :: "expr' \<times> expr'"
fun m_ctx :: "(expr' \<times> expr') list \<Rightarrow> (lineardecision_LinearDecisionRationalMP.expr' \<times> lineardecision_LinearDecisionRationalMP.expr') list"
  where "m_ctx (Nil :: (expr' \<times> expr') list) = (Nil :: (lineardecision_LinearDecisionRationalMP.expr' \<times> lineardecision_LinearDecisionRationalMP.expr') list)"
      | "m_ctx (Cons h t1) = Cons (m_eq h) (m_ctx t1)" for h t1
axiomatization where m_ctx'spec'1:   "lineardecision_LinearDecisionRationalMP.interp_ctx' (m_ctx ctx) (m_eq g) (m_y y) z = True \<longleftrightarrow> interp_ctx' ctx g y z = True"
 if "pos_ctx' ctx z"
 and "pos_eq' g z"
  for ctx :: "(expr' \<times> expr') list"
  and z :: "int \<Rightarrow> int"
  and g :: "expr' \<times> expr'"
  and y :: "int \<Rightarrow> int"
axiomatization where m_ctx'spec'0:   "length (m_ctx ctx) = length ctx"
  for ctx :: "(expr' \<times> expr') list"
axiomatization where m_ctx'spec:   "lineardecision_LinearDecisionRationalMP.valid_ctx' (m_ctx ctx)"
 if "valid_ctx' ctx"
  for ctx :: "(expr' \<times> expr') list"
end
