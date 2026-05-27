theory float_quat_integrate_Why3_ide_VCfloat_quat_integrate_call_cosf_pre_finite_arg_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_airborne_float_quat_integrate_lib.Axiomatic15_Axiomatic15" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "frama_c_airborne_float_quat_integrate_lib.Compound_Compound"
begin
theorem goal2:
  fixes t_1 :: "addr \<Rightarrow> real"
  fixes a :: "addr"
  fixes r :: "real"
  fixes r_1 :: "real"
  fixes t :: "int \<Rightarrow> int"
  shows "let r_3 :: real = t_1 (shift a (0 :: int)); r_4 :: real = t_1 (shift a (1 :: int)); r_5 :: real = t_1 (shift a (2 :: int)); r_6 :: real = r_3 * r_3 + r_4 * r_4 + r_5 * r_5; r_7 :: real = (1 :: Real.real) / (2 :: Real.real) * r * r_1 in (0 :: Real.real) \<le> r \<longrightarrow> (1 :: Real.real) / (85070591730234615865843651857942052864 :: Real.real) < r \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (0 :: Real.real) \<le> r_6 \<longrightarrow> linked t \<longrightarrow> is_finite32 r \<longrightarrow> is_float32 r \<longrightarrow> is_float32 r_1 \<longrightarrow> p_rvalid_floatrates t t_1 a \<longrightarrow> is_float32 r_3 \<longrightarrow> is_float32 r_4 \<longrightarrow> is_float32 r_5 \<longrightarrow> is_float32 r_7 \<longrightarrow> is_finite32 r_6 \<longrightarrow> is_finite32 r_7"
  sorry
end
