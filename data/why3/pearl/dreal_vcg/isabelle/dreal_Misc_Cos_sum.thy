theory dreal_Misc_Cos_sum
  imports "NTP4Verif.NTP4Verif"
begin
consts exp_limit_fun :: "real \<Rightarrow> unit"
axiomatization where exp_limit_fun_def:   "exp_limit_fun x = ()"
 if "abs x \<le> (25 :: Real.real)"
  for x :: "real"
axiomatization where exp_limit_fun'spec:   "exp x \<le> (72004899338 :: Real.real)"
 if "abs x \<le> (25 :: Real.real)"
  for x :: "real"
theorem Cos_sum:
  fixes x :: "real"
  fixes y :: "real"
  shows "cos (x + y) = cos x * cos y - sin x * sin y"
  sorry
end
