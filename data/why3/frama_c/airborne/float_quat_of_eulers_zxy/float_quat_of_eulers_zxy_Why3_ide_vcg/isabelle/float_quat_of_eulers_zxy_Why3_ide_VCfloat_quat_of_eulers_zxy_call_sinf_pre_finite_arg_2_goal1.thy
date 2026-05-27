theory float_quat_of_eulers_zxy_Why3_ide_VCfloat_quat_of_eulers_zxy_call_sinf_pre_finite_arg_2_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_airborne_float_quat_of_eulers_zxy_lib.Axiomatic15_Axiomatic15" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "frama_c_airborne_float_quat_of_eulers_zxy_lib.Compound_Compound" "Why3STD.Square_Square"
begin
theorem goal1:
  fixes t_1 :: "addr \<Rightarrow> real"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let r :: real = t_1 (shift a (0 :: int)); r_1 :: real = r / (2 :: Real.real); r_2 :: real = sin r_1; r_3 :: real = cos r_1; r_4 :: real = t_1 (shift a (1 :: int)); r_5 :: real = r_4 / (2 :: Real.real) in region (base a) \<le> (0 :: int) \<longrightarrow> r_2 \<le> (1 :: Real.real) \<longrightarrow> r_3 \<le> (1 :: Real.real) \<longrightarrow> -(1 :: Real.real) \<le> r_2 \<longrightarrow> -(1 :: Real.real) \<le> r_3 \<longrightarrow> linked t \<longrightarrow> p_rvalid_floateulers t t_1 a \<longrightarrow> is_float32 r \<longrightarrow> is_float32 (t_1 (shift a (2 :: int))) \<longrightarrow> is_float32 r_4 \<longrightarrow> is_finite32 r_1 \<longrightarrow> is_float32 r_1 \<longrightarrow> is_float32 r_5 \<longrightarrow> is_finite32 r_2 \<longrightarrow> is_finite32 r_3 \<longrightarrow> is_float32 r_2 \<longrightarrow> is_float32 r_3 \<longrightarrow> is_finite32 r_5"
  sorry
end
