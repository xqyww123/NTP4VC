theory lineardecision_MP64Coeffs_zero_expqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs"
begin
typedecl  evars
datatype  exp = Lit "int" | Var "int" | Plus "exp" "exp" | Minus "exp" | Sub "exp" "exp"
typedecl  t
definition qinterp :: "int \<times> int \<Rightarrow> real"
  where "qinterp q = (case q of (n, d) \<Rightarrow> real_of_int n / real_of_int d)" for q
fun interp_exp :: "exp \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int"
  where "interp_exp (Lit n) y = n" for n y
      | "interp_exp (Var v) y = y v" for v y
      | "interp_exp (Plus e1 e2) y = interp_exp e1 y + interp_exp e2 y" for e1 e2 y
      | "interp_exp (Sub e1 e2) y = interp_exp e1 y - interp_exp e2 y" for e1 e2 y
      | "interp_exp (Minus e') y = -interp_exp e' y" for e' y
definition minterp :: "(int \<times> int) \<times> exp \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> real"
  where "minterp t1 y = (case t1 of (q, e) \<Rightarrow> qinterp q * real_of_int ((18446744073709551615 :: int) + (1 :: int)) powr real_of_int (interp_exp e y))" for t1 y
theorem zero_exp'vc:
  fixes e :: "exp"
  shows "\<forall>(e :: exp). (case e of Lit n \<Rightarrow> True | Var _ \<Rightarrow> True | Minus e1 \<Rightarrow> (case e of Lit _ \<Rightarrow> False | Var _ \<Rightarrow> False | Plus f f1 \<Rightarrow> f = e1 \<or> f1 = e1 | Minus f \<Rightarrow> f = e1 | Sub f f1 \<Rightarrow> f = e1 \<or> f1 = e1) | Plus e1 e2 \<Rightarrow> (case e of Lit _ \<Rightarrow> False | Var _ \<Rightarrow> False | Plus f f1 \<Rightarrow> f = e1 \<or> f1 = e1 | Minus f \<Rightarrow> f = e1 | Sub f f1 \<Rightarrow> f = e1 \<or> f1 = e1) \<and> ((\<forall>(y :: int \<Rightarrow> int). interp_exp e1 y = (0 :: int)) \<longrightarrow> (case e of Lit _ \<Rightarrow> False | Var _ \<Rightarrow> False | Plus f f1 \<Rightarrow> f = e2 \<or> f1 = e2 | Minus f \<Rightarrow> f = e2 | Sub f f1 \<Rightarrow> f = e2 \<or> f1 = e2)) | Sub e1 e2 \<Rightarrow> (case e of Lit _ \<Rightarrow> False | Var _ \<Rightarrow> False | Plus f f1 \<Rightarrow> f = e1 \<or> f1 = e1 | Minus f \<Rightarrow> f = e1 | Sub f f1 \<Rightarrow> f = e1 \<or> f1 = e1) \<and> ((\<forall>(y :: int \<Rightarrow> int). interp_exp e1 y = (0 :: int)) \<longrightarrow> (case e of Lit _ \<Rightarrow> False | Var _ \<Rightarrow> False | Plus f f1 \<Rightarrow> f = e2 \<or> f1 = e2 | Minus f \<Rightarrow> f = e2 | Sub f f1 \<Rightarrow> f = e2 \<or> f1 = e2))) \<and> ((case e of Lit n \<Rightarrow> True = (if n = (0 :: int) then True else False) | Var _ \<Rightarrow> True = False | Minus e1 \<Rightarrow> (\<forall>(y :: int \<Rightarrow> int). interp_exp e1 y = (0 :: int)) | Plus e1 e2 \<Rightarrow> (\<exists>(o1 :: bool). (o1 = True \<longrightarrow> (\<forall>(y :: int \<Rightarrow> int). interp_exp e1 y = (0 :: int))) \<and> (if o1 = True then \<forall>(y :: int \<Rightarrow> int). interp_exp e2 y = (0 :: int) else True = False)) | Sub e1 e2 \<Rightarrow> (\<exists>(o1 :: bool). (o1 = True \<longrightarrow> (\<forall>(y :: int \<Rightarrow> int). interp_exp e1 y = (0 :: int))) \<and> (if o1 = True then \<forall>(y :: int \<Rightarrow> int). interp_exp e2 y = (0 :: int) else True = False))) \<longrightarrow> (\<forall>(y :: int \<Rightarrow> int). interp_exp e y = (0 :: int)))"
  and "\<forall>(e' :: exp). (\<forall>(y :: int \<Rightarrow> int). interp_exp e' y = interp_exp (Lit (0 :: int)) y + interp_exp e y) \<longrightarrow> (\<forall>(y :: int \<Rightarrow> int). interp_exp e' y = (0 :: int)) \<longrightarrow> (\<forall>(y :: int \<Rightarrow> int). interp_exp e y = (0 :: int))"
  sorry
end
