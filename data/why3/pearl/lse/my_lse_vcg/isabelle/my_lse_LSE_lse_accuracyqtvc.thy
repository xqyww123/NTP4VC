theory my_lse_LSE_lse_accuracyqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_lse_lib.udouble_UDouble" "Why3STD.ieee_float_RoundingMode" "pearl_lse_lib.my_exp_log_ExpLogLemmas" "pearl_lse_lib.my_exp_log_ExpLogApprox" "pearl_lse_lib.sum_real_Sum" "pearl_lse_lib.my_sum_Sum" "pearl_lse_lib.my_sum_Bound" "pearl_lse_lib.my_sum_Combine"
begin
consts exp_fun :: "(int \<Rightarrow> udouble) \<Rightarrow> int \<Rightarrow> real"
axiomatization where exp_fun'def:   "exp_fun a i = exp (real_fun a i)"
  for a :: "int \<Rightarrow> udouble"
  and i :: "int"
consts u_exp_fun :: "(int \<Rightarrow> udouble) \<Rightarrow> int \<Rightarrow> udouble"
axiomatization where u_exp_fun'def:   "u_exp_fun a i = u_exp (a i)"
  for a :: "int \<Rightarrow> udouble"
  and i :: "int"
definition u_sum_of_u_exp :: "(int \<Rightarrow> udouble) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> udouble"
  where "u_sum_of_u_exp a m n = u_sum (u_exp_fun a) m n" for a m n
definition lse_exact :: "(int \<Rightarrow> udouble) \<Rightarrow> int \<Rightarrow> real"
  where "lse_exact f size = ln (sum (exp_fun f) (0 :: int) size)" for f size
theorem lse_accuracy'vc:
  fixes size :: "int"
  fixes a :: "int \<Rightarrow> udouble"
  assumes fact0: "(1 :: int) \<le> size"
  assumes fact1: "real_of_int (size - (1 :: int)) \<le> (2251799813685248 :: Real.real)"
  assumes fact2: "\<forall>(i :: int). (0 :: int) \<le> i \<and> i < size \<longrightarrow> abs (to_real (a i)) \<le> exp_max_value"
  assumes fact3: "exp exp_max_value * ((1 :: Real.real) + exp_error) * real_of_int size * ((1 :: Real.real) + (1 :: Real.real) / (9007199254740992) / ((1 :: Real.real) + (1 :: Real.real) / (9007199254740992)) * real_of_int (size - (1 :: int))) \<le> log_max_value"
  shows "abs (to_real (u_log (u_sum_of_u_exp a (0 :: int) size)) - lse_exact a size) \<le> log_error * abs (lse_exact a size) - ln ((1 :: Real.real) - (exp_error + (1 :: Real.real) / (9007199254740992) / ((1 :: Real.real) + (1 :: Real.real) / (9007199254740992)) * real_of_int (size - (1 :: int)) * ((1 :: Real.real) + exp_error))) * ((1 :: Real.real) + log_error)"
  sorry
end
