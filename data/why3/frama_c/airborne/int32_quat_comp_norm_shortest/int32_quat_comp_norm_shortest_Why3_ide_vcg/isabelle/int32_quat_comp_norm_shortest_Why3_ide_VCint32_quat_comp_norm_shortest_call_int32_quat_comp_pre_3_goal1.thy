theory int32_quat_comp_norm_shortest_Why3_ide_VCint32_quat_comp_norm_shortest_call_int32_quat_comp_pre_3_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_airborne_int32_quat_comp_norm_shortest_lib.Compound_Compound" "frama_c_airborne_int32_quat_comp_norm_shortest_lib.Axiomatic15_Axiomatic15"
begin
theorem goal1:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 (shift a_1 (0 :: int)); x_1 :: int = t_1 (shift a_1 (1 :: int)); x_2 :: int = t_1 (shift a_1 (2 :: int)); x_3 :: int = t_1 (shift a_1 (3 :: int)) in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> separated a_1 (4 :: int) a (4 :: int) \<longrightarrow> is_sint32 (t_1 (shift a (0 :: int))) \<longrightarrow> is_sint32 x \<longrightarrow> is_sint32 (t_1 (shift a (1 :: int))) \<longrightarrow> is_sint32 x_1 \<longrightarrow> is_sint32 (t_1 (shift a (2 :: int))) \<longrightarrow> is_sint32 x_2 \<longrightarrow> is_sint32 (t_1 (shift a (3 :: int))) \<longrightarrow> is_sint32 x_3 \<longrightarrow> p_rvalid_bound_int32quat t t_1 a (13777 :: int) \<longrightarrow> p_rvalid_bound_int32quat t t_1 a_1 (13777 :: int) \<longrightarrow> -(23170 :: int) \<le> x \<and> -(23170 :: int) \<le> x_1 \<and> -(23170 :: int) \<le> x_2 \<and> -(23170 :: int) \<le> x_3 \<and> x \<le> (23170 :: int) \<and> x_1 \<le> (23170 :: int) \<and> x_2 \<le> (23170 :: int) \<and> x_3 \<le> (23170 :: int)"
  sorry
end
