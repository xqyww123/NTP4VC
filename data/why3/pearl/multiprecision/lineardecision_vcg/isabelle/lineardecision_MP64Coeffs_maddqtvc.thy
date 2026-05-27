theory lineardecision_MP64Coeffs_maddqtvc
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
theorem madd'vc:
  fixes b :: "int"
  fixes b1 :: "int"
  fixes b2 :: "exp"
  fixes a :: "int"
  fixes a1 :: "int"
  fixes a2 :: "exp"
  shows "let b3 :: (int \<times> int) \<times> exp = ((b, b1), b2); a3 :: (int \<times> int) \<times> exp = ((a, a1), a2); x :: int \<times> int = (b, b1); x1 :: int \<times> int = (a, a1) in if req x1 (0 :: int, 1 :: int) then \<forall>(y :: int \<Rightarrow> int). minterp b3 y = minterp a3 y + minterp b3 y else if req x (0 :: int, 1 :: int) then \<forall>(y :: int \<Rightarrow> int). minterp a3 y = minterp a3 y + minterp b3 y else (\<forall>(y :: int \<Rightarrow> int). interp_exp a2 y = interp_exp b2 y) \<longrightarrow> (\<forall>(q :: int) (q1 :: int). let q2 :: int \<times> int = (q, q1) in (\<forall>(y :: int \<Rightarrow> real). rinterp q2 y = rinterp x1 y + rinterp x y) \<longrightarrow> (\<forall>(y :: int \<Rightarrow> int). minterp (q2, a2) y = minterp a3 y + minterp b3 y))"
  sorry
end
