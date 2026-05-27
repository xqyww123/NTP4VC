theory int32_quat_of_rmat_Why3_ide_VCint32_quat_of_rmat_call_int32_sqrt_pre_4_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.real_Truncate" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_airborne_int32_quat_of_rmat_lib.Compound_Compound" "frama_c_airborne_int32_quat_of_rmat_lib.Axiomatic15_Axiomatic15" "Why3STD.Cint_Cint" "Why3STD.Cbits_Cbits" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat"
begin
theorem goal3:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); x :: int = t_1 (shift a_1 (4 :: int)); x_1 :: int = t_1 (shift a_1 (8 :: int)); x_2 :: int = t_1 (shift a_1 (0 :: int)); x_3 :: int = x_2 + x + x_1 in region (base a) \<le> (0 :: int) \<longrightarrow> x \<le> x_1 \<longrightarrow> x_3 \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> p_rvalid_bound_int32rmat t t_1 a (32767 :: int) \<longrightarrow> is_sint32 x_2 \<longrightarrow> is_sint32 (t_1 (shift a_1 (1 :: int))) \<longrightarrow> is_sint32 (t_1 (shift a_1 (2 :: int))) \<longrightarrow> is_sint32 (t_1 (shift a_1 (3 :: int))) \<longrightarrow> is_sint32 x \<longrightarrow> is_sint32 (t_1 (shift a_1 (5 :: int))) \<longrightarrow> is_sint32 (t_1 (shift a_1 (6 :: int))) \<longrightarrow> is_sint32 (t_1 (shift a_1 (7 :: int))) \<longrightarrow> is_sint32 x_1 \<longrightarrow> is_sint32 x_3 \<longrightarrow> x_2 \<le> x \<or> x_2 \<le> x_1 \<longrightarrow> to_uint32 (lsl (to_sint32 (truncate (real_of_int (x_1 - x_2 - x) + (1 :: Real.real) * (16384 :: Real.real)))) (14 :: int)) \<le> (2147483647 :: int)"
  sorry
end
