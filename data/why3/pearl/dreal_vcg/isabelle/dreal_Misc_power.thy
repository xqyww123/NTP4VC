theory dreal_Misc_power
  imports "NTP4Verif.NTP4Verif"
begin
consts exp_limit_fun :: "real \<Rightarrow> unit"
axiomatization where exp_limit_fun_def:   "exp_limit_fun x = ()"
 if "abs x \<le> (25 :: Real.real)"
  for x :: "real"
axiomatization where exp_limit_fun'spec:   "exp x \<le> (72004899338 :: Real.real)"
 if "abs x \<le> (25 :: Real.real)"
  for x :: "real"
theorem power:
  fixes x :: "real"
  assumes fact0: "x powr (2 :: Real.real) \<le> (9 :: Real.real)"
  shows "abs x \<le> (3 :: Real.real)"
  sorry
end
