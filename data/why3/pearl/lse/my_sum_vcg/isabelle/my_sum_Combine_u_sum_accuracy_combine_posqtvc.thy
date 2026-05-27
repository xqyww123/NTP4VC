theory my_sum_Combine_u_sum_accuracy_combine_posqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_lse_lib.my_sum_Sum" "pearl_lse_lib.sum_real_Sum" "pearl_lse_lib.udouble_UDouble" "Why3STD.ieee_float_RoundingMode"
begin
theorem u_sum_accuracy_combine_pos'vc:
  fixes a :: "int"
  fixes b :: "int"
  fixes f' :: "int \<Rightarrow> udouble"
  fixes f :: "int \<Rightarrow> real"
  fixes rel_err :: "real"
  fixes abs_err :: "real"
  assumes fact0: "\<forall>(i :: int). a \<le> i \<and> i < b \<longrightarrow> abs (real_fun f' i - f i) \<le> abs (f i) * rel_err + abs_err"
  assumes fact1: "\<forall>(i :: int). a \<le> i \<and> i < b \<longrightarrow> (0 :: Real.real) \<le> f i"
  assumes fact2: "(0 :: Real.real) \<le> rel_err"
  assumes fact3: "rel_err \<le> (1 :: Real.real)"
  assumes fact4: "(0 :: Real.real) \<le> abs_err"
  assumes fact5: "abs_err \<le> (1 :: Real.real)"
  assumes fact6: "(0 :: int) \<le> b - a"
  shows "abs (to_real (u_sum f' a b) - sum f a b) \<le> sum f a b * (rel_err + (1 :: Real.real) / (9007199254740992) / ((1 :: Real.real) + (1 :: Real.real) / (9007199254740992)) * real_of_int (b - a - (1 :: int)) * ((1 :: Real.real) + rel_err)) + abs_err * (((1 :: Real.real) + (1 :: Real.real) / (9007199254740992) / ((1 :: Real.real) + (1 :: Real.real) / (9007199254740992)) * real_of_int (b - a - (1 :: int))) * real_of_int (b - a))"
  sorry
end
