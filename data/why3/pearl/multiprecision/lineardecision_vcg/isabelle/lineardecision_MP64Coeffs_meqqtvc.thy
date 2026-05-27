theory lineardecision_MP64Coeffs_meqqtvc
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
fun pure_same_exp :: "exp \<Rightarrow> exp \<Rightarrow> _"
  where "pure_same_exp (Lit n1) (Lit n2) = (n1 = n2)" for n1 n2
      | "pure_same_exp (Var v1) (Var v2) = (v1 = v2)" for v1 v2
      | "pure_same_exp (Minus e1') (Minus e2') = pure_same_exp e1' e2'" for e1' e2'
      | "pure_same_exp (Plus a1 a2) (Plus b1 b2) = (pure_same_exp a1 b1 \<and> pure_same_exp a2 b2 \<or> pure_same_exp a1 b2 \<and> pure_same_exp a2 b1)" for a1 a2 b1 b2
      | "pure_same_exp x x0 = False" for x x0
axiomatization where pure_same_exp'spec:   "interp_exp e1 y = interp_exp e2 y"
 if "pure_same_exp e1 e2"
  for e1 :: "exp"
  and e2 :: "exp"
  and y :: "int \<Rightarrow> int"
theorem meq'vc:
  fixes b :: "int"
  fixes b1 :: "int"
  fixes a :: "int"
  fixes a1 :: "int"
  fixes a2 :: "exp"
  fixes b2 :: "exp"
  fixes y :: "int \<Rightarrow> int"
  assumes fact0: "let x :: int \<times> int = (b, b1); x1 :: int \<times> int = (a, a1) in \<exists>(o1 :: bool). ((req x1 x \<longrightarrow> (\<forall>(y :: int \<Rightarrow> real). rinterp x1 y = rinterp x y)) \<and> (if req x1 x then o1 = (if pure_same_exp a2 b2 then True else False) \<and> (o1 = True \<longrightarrow> (\<forall>(y :: int \<Rightarrow> int). interp_exp a2 y = interp_exp b2 y)) else o1 = False)) \<and> (if o1 = True then True else if req x1 (0 :: int, 1 :: int) then True = (if req x (0 :: int, 1 :: int) then True else False) else True = False)"
  shows "minterp ((a, a1), a2) y = minterp ((b, b1), b2) y"
  sorry
end
