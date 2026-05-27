theory my_sum_Sum_u_sumqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_lse_lib.sum_real_Sum" "pearl_lse_lib.udouble_UDouble" "Why3STD.ieee_float_RoundingMode"
begin
theorem u_sum'vc:
  fixes n :: "int"
  fixes m :: "int"
  assumes fact0: "\<not>n \<le> m"
  shows "(0 :: int) \<le> n - m"
  and "n - (1 :: int) - m < n - m"
  sorry
end
