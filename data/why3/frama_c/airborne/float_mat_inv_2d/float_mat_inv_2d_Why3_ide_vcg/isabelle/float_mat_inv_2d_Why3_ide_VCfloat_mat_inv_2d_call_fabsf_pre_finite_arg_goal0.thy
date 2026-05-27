theory float_mat_inv_2d_Why3_ide_VCfloat_mat_inv_2d_call_fabsf_pre_finite_arg_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "frama_c_airborne_float_mat_inv_2d_lib.Compound_Compound"
begin
theorem goal0:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> real"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); r :: real = t_1 a_2; r_1 :: real = t_1 (shift a (1 :: int)); r_2 :: real = t_1 (shift a (2 :: int)); r_3 :: real = t_1 (shift a (3 :: int)); r_4 :: real = r * r_3 + -(r_1 * r_2) in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_float32 r \<longrightarrow> is_float32 r_1 \<longrightarrow> is_float32 r_2 \<longrightarrow> is_float32 r_3 \<longrightarrow> valid_rd t a_2 (4 :: int) \<longrightarrow> valid_rw t (shift a_1 (0 :: int)) (4 :: int) \<longrightarrow> is_float32 r_4 \<longrightarrow> is_finite32 r_4"
  sorry
end
