theory dreal_Misc_sqr_sqrt_KO
  imports "NTP4Verif.NTP4Verif"
begin
consts exp_limit_fun :: "real \<Rightarrow> unit"
axiomatization where exp_limit_fun_def:   "exp_limit_fun x = ()"
 if "abs x \<le> (25 :: Real.real)"
  for x :: "real"
axiomatization where exp_limit_fun'spec:   "exp x \<le> (72004899338 :: Real.real)"
 if "abs x \<le> (25 :: Real.real)"
  for x :: "real"
theorem sqr_sqrt_KO:
  fixes x :: "real"
  assumes fact0: "(0 :: Real.real) \<le> x"
  shows "sqrt x ^ (2) = x"
  sorry
end
