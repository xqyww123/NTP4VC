theory my_exp_log_ExpLogApprox_u_exp_posqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_lse_lib.my_exp_log_ExpLogLemmas" "pearl_lse_lib.udouble_UDouble" "Why3STD.ieee_float_RoundingMode"
begin
consts exp_max_value :: "real"
axiomatization where exp_max_value_spec:   "(0 :: Real.real) < exp_max_value"
consts exp_error :: "real"
axiomatization where exp_error_bound'0:   "(0 :: Real.real) < exp_error"
axiomatization where exp_error_bound'1:   "exp_error \<le> (1 :: Real.real) / (2)"
consts u_exp :: "udouble \<Rightarrow> udouble"
axiomatization where u_exp_spec:   "abs (to_real (u_exp x) - exp (to_real x)) \<le> exp (to_real x) * exp_error"
 if "abs (to_real x) \<le> exp_max_value"
  for x :: "udouble"
theorem u_exp_pos'vc:
  fixes x :: "udouble"
  assumes fact0: "abs (to_real x) \<le> exp_max_value"
  shows "(0 :: Real.real) < to_real (u_exp x)"
  sorry
end
