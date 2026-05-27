theory cpumask_copy_Why3_ide_VCcpumask_copy_assert_rte_signed_overflow_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_should_we_balance_lib.A_thread_variables_properties_A_thread_variables_properties" "frama_c_should_we_balance_lib.Compound_Compound"
begin
theorem goal9:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a_1 (0 :: int); a_4 :: addr = t_3 a_2; a_5 :: addr = shift a_4 (0 :: int); a_6 :: addr = shift a_4 i; a_7 :: addr = t_3 a_3; a_8 :: addr = shift a_7 (0 :: int); a_9 :: addr \<Rightarrow> int = havoc t_1 t_2 a_8 l_size; a_10 :: int = a_9 a_6 in \<not>to_uint32 i = l_size \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i \<le> l_size \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> valid_rd t a (1 :: int) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_5 l_size \<longrightarrow> valid_rd t a_6 (1 :: int) \<longrightarrow> valid_rw t a_8 l_size \<longrightarrow> valid_rw t (shift a_7 i) (1 :: int) \<longrightarrow> separated a_8 l_size a_5 l_size \<longrightarrow> is_uint8 a_10 \<longrightarrow> a_10 = (0 :: int) \<or> a_10 = (1 :: int) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> \<not>a_9 (shift a_7 i_1) = (0 :: int) \<longleftrightarrow> \<not>a_9 (shift a_4 i_1) = (0 :: int)) \<longrightarrow> i \<le> (2147483646 :: int)"
  sorry
end
