theory cpumask_copy_Why3_ide_VCcpumask_copy_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_should_we_balance_lib.A_thread_variables_properties_A_thread_variables_properties" "frama_c_should_we_balance_lib.Compound_Compound"
begin
theorem goal0:
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = t_3 (shift a (0 :: int)); a_3 :: addr = shift a_2 (0 :: int); a_4 :: addr = t_3 (shift a_1 (0 :: int)); a_5 :: addr = shift a_4 (0 :: int); a_6 :: addr \<Rightarrow> int = havoc t_1 t_2 a_5 l_size in to_uint32 i_1 = l_size \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i < l_size \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 \<le> l_size \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> is_sint32 i_1 \<longrightarrow> valid_rd t a (1 :: int) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rd t a_3 l_size \<longrightarrow> valid_rw t a_5 l_size \<longrightarrow> separated a_5 l_size a_3 l_size \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> \<not>a_6 (shift a_4 i_2) = (0 :: int) \<longleftrightarrow> \<not>a_6 (shift a_2 i_2) = (0 :: int)) \<longrightarrow> \<not>a_6 (shift a_4 i) = (0 :: int) \<longleftrightarrow> \<not>a_6 (shift a_2 i) = (0 :: int)"
  sorry
end
