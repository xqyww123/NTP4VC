theory my_sum_Bound_u_sum_constant_boundsqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_lse_lib.my_sum_Sum" "pearl_lse_lib.sum_real_Sum" "pearl_lse_lib.udouble_UDouble" "Why3STD.ieee_float_RoundingMode"
begin
theorem u_sum_constant_bounds'vc:
  fixes n :: "int"
  fixes m :: "int"
  fixes size :: "int"
  fixes max :: "real"
  fixes a :: "int \<Rightarrow> udouble"
  assumes fact0: "(0 :: int) \<le> n - m"
  assumes fact1: "n - m \<le> size"
  assumes fact2: "(0 :: Real.real) \<le> max"
  assumes fact3: "\<forall>(i :: int). m \<le> i \<and> i < n \<longrightarrow> abs (to_real (a i)) \<le> max"
  shows "let o1 :: int \<Rightarrow> real = real_fun a; o2 :: real = -max in (m \<le> n \<and> (\<forall>(i :: int). m \<le> i \<and> i < n \<longrightarrow> o2 \<le> o1 i \<and> o1 i \<le> max)) \<and> (real_of_int (n - m) * o2 \<le> sum o1 m n \<and> sum o1 m n \<le> real_of_int (n - m) * max \<longrightarrow> (let o3 :: int \<Rightarrow> real = abs_real_fun a in (m \<le> n \<and> (\<forall>(i :: int). m \<le> i \<and> i < n \<longrightarrow> (0 :: Real.real) \<le> o3 i \<and> o3 i \<le> max)) \<and> (real_of_int (n - m) * (0 :: Real.real) \<le> sum o3 m n \<and> sum o3 m n \<le> real_of_int (n - m) * max \<longrightarrow> abs (to_real (u_sum a m n)) \<le> max * real_of_int size * ((1 :: Real.real) + (1 :: Real.real) / (9007199254740992) / ((1 :: Real.real) + (1 :: Real.real) / (9007199254740992)) * real_of_int (size - (1 :: int))))))"
  sorry
end
