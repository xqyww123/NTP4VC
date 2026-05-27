theory float_quat_differential_Why3_ide_VCfloat_quat_differential_call_sqrtf_pre_finite_arg_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_airborne_float_quat_differential_lib.Axiomatic15_Axiomatic15" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "frama_c_airborne_float_quat_differential_lib.Compound_Compound"
begin
theorem goal0:
  fixes t_1 :: "addr \<Rightarrow> real"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let r :: real = t_1 (shift a (0 :: int)); r_1 :: real = t_1 (shift a (1 :: int)); r_2 :: real = t_1 (shift a (2 :: int)) in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> p_valid_floatquat t t_1 a_1 \<longrightarrow> p_rvalid_floatrates t t_1 a \<longrightarrow> is_float32 r \<longrightarrow> is_float32 r_1 \<longrightarrow> is_float32 r_2 \<longrightarrow> is_finite32 (r * r + r_1 * r_1 + r_2 * r_2)"
  sorry
end
