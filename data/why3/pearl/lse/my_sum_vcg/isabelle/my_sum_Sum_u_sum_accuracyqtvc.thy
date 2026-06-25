theory my_sum_Sum_u_sum_accuracyqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_lse_lib.sum_real_Sum" "pearl_lse_lib.udouble_UDouble" "Why3STD.ieee_float_RoundingMode"
begin
consts u_sum :: "(int \<Rightarrow> udouble) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> udouble"
axiomatization where u_sum_def:   "if n \<le> m then u_sum a m n = uzero else u_sum a m n = uadd (u_sum a m (n - (1 :: int))) (a (n - (1 :: int)))"
  for n :: "int"
  and m :: "int"
  and a :: "int \<Rightarrow> udouble"
consts real_fun :: "(int \<Rightarrow> udouble) \<Rightarrow> int \<Rightarrow> real"
axiomatization where real_fun_def:   "real_fun a i = to_real (a i)"
  for a :: "int \<Rightarrow> udouble"
  and i :: "int"
consts abs_real_fun :: "(int \<Rightarrow> udouble) \<Rightarrow> int \<Rightarrow> real"
axiomatization where abs_real_fun_def:   "abs_real_fun a i = abs (to_real (a i))"
  for a :: "int \<Rightarrow> udouble"
  and i :: "int"
theorem u_sum_accuracy'vc:
  fixes m :: "int"
  fixes n :: "int"
  fixes a :: "int \<Rightarrow> udouble"
  assumes fact0: "m \<le> n"
  shows "abs (to_real (u_sum a m n) - sum (real_fun a) m n) \<le> real_of_int (n - m - (1 :: int)) * ((1 :: Real.real) / (9007199254740992) / ((1 :: Real.real) + (1 :: Real.real) / (9007199254740992))) * sum (abs_real_fun a) m n"
  sorry
end
