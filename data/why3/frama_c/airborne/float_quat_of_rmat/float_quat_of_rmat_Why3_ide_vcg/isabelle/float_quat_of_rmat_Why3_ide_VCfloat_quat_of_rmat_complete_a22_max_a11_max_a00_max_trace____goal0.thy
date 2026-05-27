theory float_quat_of_rmat_Why3_ide_VCfloat_quat_of_rmat_complete_a22_max_a11_max_a00_max_trace____goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_airborne_float_quat_of_rmat_lib.Axiomatic15_Axiomatic15" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "frama_c_airborne_float_quat_of_rmat_lib.Compound_Compound" "frama_c_airborne_float_quat_of_rmat_lib.Axiomatic17_Axiomatic17" "frama_c_airborne_float_quat_of_rmat_lib.S10_RealRMat_s_S10_RealRMat_s" "frama_c_airborne_float_quat_of_rmat_lib.Axiomatic19_Axiomatic19" "frama_c_airborne_float_quat_of_rmat_lib.S11_RealQuat_s_S11_RealQuat_s" "Why3STD.Square_Square"
begin
theorem goal0:
  fixes t_1 :: "addr \<Rightarrow> real"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: s10_realrmat_s = l_l_rmat_of_floatrmat t_1 a; a_3 :: addr = shift a (0 :: int); r :: real = t_1 (shift a_3 (0 :: int)); r_1 :: real = t_1 (shift a_3 (4 :: int)); r_2 :: real = t_1 (shift a_3 (8 :: int)); r_3 :: real = l_trace_2' t_1 a in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> valid_rw t a_1 (4 :: int) \<longrightarrow> p_rvalid_floatrmat t t_1 a \<longrightarrow> separated a (9 :: int) a_1 (4 :: int) \<longrightarrow> p_rotation_matrix a_2 \<longrightarrow> p_special_orthogonal a_2 \<longrightarrow> is_float32 r \<longrightarrow> is_float32 r_1 \<longrightarrow> is_float32 r_2 \<longrightarrow> (0 :: Real.real) < r_3 \<or> r_3 \<le> (0 :: Real.real) \<and> r_1 < r \<and> r_2 < r \<or> r_3 \<le> (0 :: Real.real) \<and> r \<le> r_1 \<and> r_2 < r_1 \<or> r_3 \<le> (0 :: Real.real) \<and> r \<le> r_2 \<and> r_1 \<le> r_2"
  sorry
end
