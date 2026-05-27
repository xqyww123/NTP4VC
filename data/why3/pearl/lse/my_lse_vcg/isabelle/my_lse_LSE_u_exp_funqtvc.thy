theory my_lse_LSE_u_exp_funqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_lse_lib.udouble_UDouble" "Why3STD.ieee_float_RoundingMode" "pearl_lse_lib.my_exp_log_ExpLogLemmas" "pearl_lse_lib.my_exp_log_ExpLogApprox" "pearl_lse_lib.sum_real_Sum" "pearl_lse_lib.my_sum_Sum"
begin
consts exp_fun :: "(int \<Rightarrow> udouble) \<Rightarrow> int \<Rightarrow> real"
axiomatization where exp_fun'def:   "exp_fun a i = exp (real_fun a i)"
  for a :: "int \<Rightarrow> udouble"
  and i :: "int"
theorem u_exp_fun'vc:
  shows "True"
  sorry
end
