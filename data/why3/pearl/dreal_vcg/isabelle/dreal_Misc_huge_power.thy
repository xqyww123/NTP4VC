theory dreal_Misc_huge_power
  imports "NTP4Verif.NTP4Verif"
begin
consts exp_limit_fun :: "real \<Rightarrow> unit"
axiomatization where exp_limit_fun_def:   "exp_limit_fun x = ()"
 if "abs x \<le> (25 :: Real.real)"
  for x :: "real"
axiomatization where exp_limit_fun'spec:   "exp x \<le> (72004899338 :: Real.real)"
 if "abs x \<le> (25 :: Real.real)"
  for x :: "real"
theorem huge_power:
  shows "(5 :: Real.real) powr (100 :: Real.real) \<le> (7888609100000000000000000000000000000000000000000000000000000000000000 :: Real.real)"
  sorry
end
