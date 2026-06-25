theory dreal_Misc_exp_limit_from_int_KO
  imports "NTP4Verif.NTP4Verif"
begin
consts exp_limit_fun :: "real \<Rightarrow> unit"
axiomatization where exp_limit_fun_def:   "exp_limit_fun x = ()"
 if "abs x \<le> (25 :: Real.real)"
  for x :: "real"
axiomatization where exp_limit_fun'spec:   "exp x \<le> (72004899338 :: Real.real)"
 if "abs x \<le> (25 :: Real.real)"
  for x :: "real"
theorem exp_limit_from_int_KO:
  fixes x :: "int"
  assumes fact0: "abs x \<le> (25 :: int)"
  shows "exp (real_of_int x) \<le> (72004899338 :: Real.real)"
  sorry
end
