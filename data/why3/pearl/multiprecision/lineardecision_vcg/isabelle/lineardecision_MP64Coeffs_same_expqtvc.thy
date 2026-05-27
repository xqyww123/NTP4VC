theory lineardecision_MP64Coeffs_same_expqtvc
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
theorem same_exp'vc:
  fixes e2 :: "exp"
  fixes e1 :: "exp"
  shows "case e2 of Lit x \<Rightarrow> (case e1 of Lit x1 \<Rightarrow> x1 = x \<longrightarrow> (\<forall>(y :: int \<Rightarrow> int). interp_exp e1 y = interp_exp e2 y) | _ \<Rightarrow> (\<forall>(o1 :: exp). (\<forall>(y :: int \<Rightarrow> int). interp_exp o1 y = -interp_exp e2 y) \<longrightarrow> (\<forall>(o2 :: exp). (\<forall>(y :: int \<Rightarrow> int). interp_exp o2 y = interp_exp e1 y + interp_exp o1 y) \<longrightarrow> (\<forall>(y :: int \<Rightarrow> int). interp_exp o2 y = (0 :: int)) \<longrightarrow> (\<forall>(y :: int \<Rightarrow> int). interp_exp e1 y = interp_exp e2 y)))) | Var x \<Rightarrow> (case e1 of Var x1 \<Rightarrow> x1 = x \<longrightarrow> (\<forall>(y :: int \<Rightarrow> int). interp_exp e1 y = interp_exp e2 y) | _ \<Rightarrow> (\<forall>(o1 :: exp). (\<forall>(y :: int \<Rightarrow> int). interp_exp o1 y = -interp_exp e2 y) \<longrightarrow> (\<forall>(o2 :: exp). (\<forall>(y :: int \<Rightarrow> int). interp_exp o2 y = interp_exp e1 y + interp_exp o1 y) \<longrightarrow> (\<forall>(y :: int \<Rightarrow> int). interp_exp o2 y = (0 :: int)) \<longrightarrow> (\<forall>(y :: int \<Rightarrow> int). interp_exp e1 y = interp_exp e2 y)))) | Minus x \<Rightarrow> (case e1 of Minus x1 \<Rightarrow> ((case e1 of Lit _ \<Rightarrow> False | Var _ \<Rightarrow> False | Plus f f1 \<Rightarrow> f = x1 \<or> f1 = x1 | Minus f \<Rightarrow> f = x1 | Sub f f1 \<Rightarrow> f = x1 \<or> f1 = x1) \<or> e1 = x1 \<and> (case e2 of Lit _ \<Rightarrow> False | Var _ \<Rightarrow> False | Plus f f1 \<Rightarrow> f = x \<or> f1 = x | Minus f \<Rightarrow> f = x | Sub f f1 \<Rightarrow> f = x \<or> f1 = x)) \<and> ((\<forall>(y :: int \<Rightarrow> int). interp_exp x1 y = interp_exp x y) \<longrightarrow> (\<forall>(y :: int \<Rightarrow> int). interp_exp e1 y = interp_exp e2 y)) | _ \<Rightarrow> (\<forall>(o1 :: exp). (\<forall>(y :: int \<Rightarrow> int). interp_exp o1 y = -interp_exp e2 y) \<longrightarrow> (\<forall>(o2 :: exp). (\<forall>(y :: int \<Rightarrow> int). interp_exp o2 y = interp_exp e1 y + interp_exp o1 y) \<longrightarrow> (\<forall>(y :: int \<Rightarrow> int). interp_exp o2 y = (0 :: int)) \<longrightarrow> (\<forall>(y :: int \<Rightarrow> int). interp_exp e1 y = interp_exp e2 y)))) | _ \<Rightarrow> (\<forall>(o1 :: exp). (\<forall>(y :: int \<Rightarrow> int). interp_exp o1 y = -interp_exp e2 y) \<longrightarrow> (\<forall>(o2 :: exp). (\<forall>(y :: int \<Rightarrow> int). interp_exp o2 y = interp_exp e1 y + interp_exp o1 y) \<longrightarrow> (\<forall>(y :: int \<Rightarrow> int). interp_exp o2 y = (0 :: int)) \<longrightarrow> (\<forall>(y :: int \<Rightarrow> int). interp_exp e1 y = interp_exp e2 y)))"
  sorry
end
