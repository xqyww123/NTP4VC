theory double_quat_of_eulers_Why3_ide_VCdouble_quat_of_eulers_call_sin_pre_finite_arg_2_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_airborne_double_quat_of_eulers_lib.Axiomatic19_Axiomatic19" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "frama_c_airborne_double_quat_of_eulers_lib.Compound_Compound"
begin
theorem goal1:
  fixes t_1 :: "addr \<Rightarrow> real"
  fixes a :: "addr"
  fixes r :: "real"
  fixes r_1 :: "real"
  fixes t :: "int \<Rightarrow> int"
  shows "let r_2 :: real = t_1 (shift a (0 :: int)); r_3 :: real = t_1 (shift a (1 :: int)); r_4 :: real = r_2 / (2 :: Real.real); r_5 :: real = r_3 / (2 :: Real.real) in r \<le> (1 :: Real.real) \<longrightarrow> r_1 \<le> (1 :: Real.real) \<longrightarrow> -(1 :: Real.real) \<le> r \<longrightarrow> -(1 :: Real.real) \<le> r_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_finite64 r \<longrightarrow> is_finite64 r_1 \<longrightarrow> is_float64 r \<longrightarrow> is_float64 r_1 \<longrightarrow> p_rvalid_doubleeulers t t_1 a \<longrightarrow> is_float64 r_2 \<longrightarrow> is_float64 (t_1 (shift a (2 :: int))) \<longrightarrow> is_float64 r_3 \<longrightarrow> is_finite64 r_4 \<longrightarrow> is_float64 r_4 \<longrightarrow> is_float64 r_5 \<longrightarrow> is_finite64 r_5"
  sorry
end
