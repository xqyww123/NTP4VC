theory dreal_Misc_power2
  imports "NTP4Verif.NTP4Verif"
begin
consts exp_limit_fun :: "real \<Rightarrow> unit"
axiomatization where exp_limit_fun_def:   "exp_limit_fun x = ()"
 if "abs x \<le> (25 :: Real.real)"
  for x :: "real"
axiomatization where exp_limit_fun'spec:   "exp x \<le> (72004899338 :: Real.real)"
 if "abs x \<le> (25 :: Real.real)"
  for x :: "real"
theorem power2:
  fixes x :: "real"
  assumes fact0: "(5 :: Real.real) / (2) < x"
  shows "(20 :: Real.real) < x powr (3 :: Real.real) * (2 :: Real.real)"
  sorry
end
