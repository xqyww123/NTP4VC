theory find_first_bit_Why3_ide_VCfind_first_bit_nowhere_post_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_should_we_balance_lib.Compound_Compound" "frama_c_should_we_balance_lib.A_thread_variables_properties_A_thread_variables_properties" "Why3STD.Cint_Cint"
begin
theorem goal7:
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a i_2 in i \<le> l_size \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i_3 \<longrightarrow> is_uint8 (t_1 (shift a i_1)) \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> (if i_1 < i then i_2 = i_1 \<and> to_sint32 i_2 = i_3 \<and> t_1 a_1 = (1 :: int) \<and> valid_rd t a_1 (1 :: int) else to_sint32 i = i_3) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < i \<longrightarrow> t_1 (shift a i_4) = (0 :: int)) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < i_1 \<longrightarrow> t_1 (shift a i_4) = (0 :: int)) \<longrightarrow> i_3 = i"
  sorry
end
