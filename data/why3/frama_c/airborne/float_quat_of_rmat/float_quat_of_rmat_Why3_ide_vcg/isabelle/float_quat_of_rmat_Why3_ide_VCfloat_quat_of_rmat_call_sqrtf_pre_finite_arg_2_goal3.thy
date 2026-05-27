theory float_quat_of_rmat_Why3_ide_VCfloat_quat_of_rmat_call_sqrtf_pre_finite_arg_2_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_airborne_float_quat_of_rmat_lib.Axiomatic15_Axiomatic15" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "frama_c_airborne_float_quat_of_rmat_lib.Compound_Compound" "frama_c_airborne_float_quat_of_rmat_lib.Axiomatic17_Axiomatic17" "frama_c_airborne_float_quat_of_rmat_lib.S10_RealRMat_s_S10_RealRMat_s"
begin
theorem goal3:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> real"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); r :: real = t_1 (shift a_2 (4 :: int)); r_1 :: real = t_1 (shift a_2 (0 :: int)); r_2 :: real = t_1 (shift a_2 (8 :: int)); r_3 :: real = r_1 + r + r_2; a_3 :: s10_realrmat_s = l_l_rmat_of_floatrmat t_1 a in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> r < r_1 \<longrightarrow> r_2 < r_1 \<longrightarrow> r_3 \<le> (0 :: Real.real) \<longrightarrow> linked t \<longrightarrow> valid_rw t a_1 (4 :: int) \<longrightarrow> p_rvalid_floatrmat t t_1 a \<longrightarrow> separated a (9 :: int) a_1 (4 :: int) \<longrightarrow> p_rotation_matrix a_3 \<longrightarrow> p_special_orthogonal a_3 \<longrightarrow> is_float32 r_1 \<longrightarrow> is_float32 r \<longrightarrow> is_float32 (t_1 (shift a_2 (5 :: int))) \<longrightarrow> is_float32 (t_1 (shift a_2 (7 :: int))) \<longrightarrow> is_float32 r_2 \<longrightarrow> is_float32 r_3 \<longrightarrow> is_finite32 (r_1 + -r + -r_2 + (1 :: Real.real))"
  sorry
end
