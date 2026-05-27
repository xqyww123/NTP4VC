theory cpumask_andnot_Why3_ide_VCcpumask_andnot_assert_rte_bool_value_2_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_should_we_balance_lib.A_thread_variables_properties_A_thread_variables_properties" "frama_c_should_we_balance_lib.Compound_Compound" "frama_c_should_we_balance_lib.A_schedule_cpumask_A_schedule_cpumask"
begin
theorem goal9:
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_3 :: addr = t_3 (shift a_2 (0 :: int)); a_4 :: addr = shift a_3 (0 :: int); a_5 :: addr \<Rightarrow> int = havoc t_1 t_2 a_4 l_size; a_6 :: addr = shift a_1 (0 :: int); a_7 :: addr = t_3 a_6; a_8 :: addr = shift a_7 i; a_9 :: addr = t_3 (shift a (0 :: int)); a_10 :: addr = shift a_9 (0 :: int); a_11 :: addr = shift a_7 (0 :: int); a_12 :: int = a_5 (shift a_9 i) in \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>to_uint32 i = l_size \<longrightarrow> a_5 a_8 = (1 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i \<le> l_size \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> valid_rd t a (1 :: int) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t a_6 (1 :: int) \<longrightarrow> valid_rd t a_10 l_size \<longrightarrow> valid_rd t a_11 l_size \<longrightarrow> valid_rd t a_8 (1 :: int) \<longrightarrow> valid_rw t a_4 l_size \<longrightarrow> is_uint8 a_12 \<longrightarrow> (\<not>a_2 = a \<longrightarrow> separated a_4 l_size a_10 l_size) \<longrightarrow> (\<not>a_2 = a_1 \<longrightarrow> separated a_4 l_size a_11 l_size) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < l_size \<longrightarrow> separated a_4 l_size (shift (t_3 (shift (l_cpu_smt_mask i_1) (0 :: int))) (0 :: int)) l_size) \<longrightarrow> (\<forall>(i_1 :: int). let a_13 :: addr = shift a_3 i_1 in i \<le> i_1 \<longrightarrow> i_1 < l_size \<longrightarrow> \<not>a_5 a_13 = (0 :: int) \<longleftrightarrow> \<not>t_2 a_13 = (0 :: int)) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> t_2 (shift a_9 i_1) = (0 :: int) \<and> \<not>t_2 (shift a_7 i_1) = (0 :: int) \<longleftrightarrow> \<not>a_5 (shift a_3 i_1) = (0 :: int)) \<longrightarrow> a_12 = (0 :: int) \<or> a_12 = (1 :: int)"
  sorry
end
