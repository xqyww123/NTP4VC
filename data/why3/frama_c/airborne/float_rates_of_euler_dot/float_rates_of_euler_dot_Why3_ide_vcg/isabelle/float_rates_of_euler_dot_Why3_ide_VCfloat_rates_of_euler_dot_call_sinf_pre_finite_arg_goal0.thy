theory float_rates_of_euler_dot_Why3_ide_VCfloat_rates_of_euler_dot_call_sinf_pre_finite_arg_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_airborne_float_rates_of_euler_dot_lib.Axiomatic15_Axiomatic15" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "frama_c_airborne_float_rates_of_euler_dot_lib.Compound_Compound"
begin
theorem goal0:
  fixes t_1 :: "addr \<Rightarrow> real"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let r :: real = t_1 (shift a_1 (1 :: int)) in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> p_rvalid_floateulers t t_1 a \<longrightarrow> p_rvalid_floateulers t t_1 a_1 \<longrightarrow> is_float32 (t_1 (shift a (0 :: int))) \<longrightarrow> is_float32 (t_1 (shift a_1 (0 :: int))) \<longrightarrow> is_float32 (t_1 (shift a (2 :: int))) \<longrightarrow> is_float32 (t_1 (shift a (1 :: int))) \<longrightarrow> is_float32 r \<longrightarrow> is_finite32 r"
  sorry
end
