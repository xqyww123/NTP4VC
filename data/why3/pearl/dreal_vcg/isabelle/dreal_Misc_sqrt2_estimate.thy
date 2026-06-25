theory dreal_Misc_sqrt2_estimate
  imports "NTP4Verif.NTP4Verif"
begin
consts exp_limit_fun :: "real \<Rightarrow> unit"
axiomatization where exp_limit_fun_def:   "exp_limit_fun x = ()"
 if "abs x \<le> (25 :: Real.real)"
  for x :: "real"
axiomatization where exp_limit_fun'spec:   "exp x \<le> (72004899338 :: Real.real)"
 if "abs x \<le> (25 :: Real.real)"
  for x :: "real"
theorem sqrt2_estimate:
  shows "(141421356237 :: Real.real) / (100000000000) \<le> sqrt (2 :: Real.real)"
  and "sqrt (2 :: Real.real) \<le> (70710678119 :: Real.real) / (50000000000)"
  sorry
end
