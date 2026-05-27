theory lineardecision_LinearDecisionIntMP_eqqtrefnqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs" "pearl_multiprecision_lib.lineardecision_MP64Coeffs"
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
theorem eq'refn'vc:
  shows "True"
  sorry
end
