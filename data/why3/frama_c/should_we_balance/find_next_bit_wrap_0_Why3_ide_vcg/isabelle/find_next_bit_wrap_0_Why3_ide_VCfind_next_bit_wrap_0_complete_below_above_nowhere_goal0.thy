theory find_next_bit_wrap_0_Why3_ide_VCfind_next_bit_wrap_0_complete_below_above_nowhere_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_should_we_balance_lib.A_thread_variables_properties_A_thread_variables_properties" "Why3STD.Cint_Cint" "frama_c_should_we_balance_lib.Compound_Compound"
begin
theorem goal0:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "i_1 < i"
  assumes fact1: "i \<le> l_size"
  assumes fact2: "region (base a) \<le> (0 :: int)"
  assumes fact3: "linked t"
  assumes fact4: "is_uint32 i"
  assumes fact5: "is_uint32 i_1"
  assumes fact6: "valid_rd t (shift a (0 :: int)) i"
  shows "(\<forall>(i_2 :: int). i_2 < i \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> t_1 (shift a i_2) = (0 :: int)) \<and> (\<exists>(i_2 :: int). \<not>t_1 (shift a i_2) = (0 :: int) \<and> (0 :: int) \<le> i_2 \<and> i_2 < i_1) \<or> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> t_1 (shift a i_2) = (0 :: int)) \<or> (\<exists>(i_2 :: int). \<not>t_1 (shift a i_2) = (0 :: int) \<and> i_2 < i \<and> i_1 \<le> i_2)"
  sorry
end
