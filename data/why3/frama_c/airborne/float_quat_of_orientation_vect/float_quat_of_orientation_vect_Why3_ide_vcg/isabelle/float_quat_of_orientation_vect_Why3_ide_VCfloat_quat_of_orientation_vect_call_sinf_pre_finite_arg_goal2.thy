theory float_quat_of_orientation_vect_Why3_ide_VCfloat_quat_of_orientation_vect_call_sinf_pre_finite_arg_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_airborne_float_quat_of_orientation_vect_lib.Axiomatic15_Axiomatic15" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "frama_c_airborne_float_quat_of_orientation_vect_lib.Compound_Compound"
begin
theorem goal2:
  fixes t_1 :: "addr \<Rightarrow> real"
  fixes a :: "addr"
  fixes r :: "real"
  fixes t :: "int \<Rightarrow> int"
  shows "let r_2 :: real = t_1 (shift a (0 :: int)); r_3 :: real = t_1 (shift a (1 :: int)); r_4 :: real = t_1 (shift a (2 :: int)); r_5 :: real = r_2 * r_2 + r_3 * r_3 + r_4 * r_4 in (0 :: Real.real) \<le> r \<longrightarrow> (3022314549036573 :: Real.real) / (302231454903657293676544 :: Real.real) \<le> r \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (0 :: Real.real) \<le> r_5 \<longrightarrow> linked t \<longrightarrow> is_finite32 r \<longrightarrow> is_float32 r \<longrightarrow> p_rvalid_floatvect3 t t_1 a \<longrightarrow> is_float32 r_2 \<longrightarrow> is_float32 r_3 \<longrightarrow> is_float32 r_4 \<longrightarrow> is_finite32 r_5 \<longrightarrow> is_finite32 (r / (2 :: Real.real))"
  sorry
end
