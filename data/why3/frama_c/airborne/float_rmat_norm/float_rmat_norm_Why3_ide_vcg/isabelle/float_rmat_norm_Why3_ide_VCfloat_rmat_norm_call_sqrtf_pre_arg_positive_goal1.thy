theory float_rmat_norm_Why3_ide_VCfloat_rmat_norm_call_sqrtf_pre_arg_positive_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_airborne_float_rmat_norm_lib.Axiomatic15_Axiomatic15" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "frama_c_airborne_float_rmat_norm_lib.Compound_Compound"
begin
theorem goal1:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> real"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); r :: real = t_1 (shift a_1 (0 :: int)); r_1 :: real = t_1 (shift a_1 (1 :: int)); r_2 :: real = t_1 (shift a_1 (2 :: int)); r_3 :: real = t_1 (shift a_1 (3 :: int)); r_4 :: real = t_1 (shift a_1 (4 :: int)); r_5 :: real = t_1 (shift a_1 (5 :: int)); r_6 :: real = t_1 (shift a_1 (6 :: int)); r_7 :: real = t_1 (shift a_1 (7 :: int)); r_8 :: real = t_1 (shift a_1 (8 :: int)) in region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> p_rvalid_floatrmat t t_1 a \<longrightarrow> is_float32 r \<longrightarrow> is_float32 r_1 \<longrightarrow> is_float32 r_2 \<longrightarrow> is_float32 r_3 \<longrightarrow> is_float32 r_4 \<longrightarrow> is_float32 r_5 \<longrightarrow> is_float32 r_6 \<longrightarrow> is_float32 r_7 \<longrightarrow> is_float32 r_8 \<longrightarrow> (0 :: Real.real) \<le> r * r + r_1 * r_1 + r_2 * r_2 + r_3 * r_3 + r_4 * r_4 + r_5 * r_5 + r_6 * r_6 + r_7 * r_7 + r_8 * r_8"
  sorry
end
