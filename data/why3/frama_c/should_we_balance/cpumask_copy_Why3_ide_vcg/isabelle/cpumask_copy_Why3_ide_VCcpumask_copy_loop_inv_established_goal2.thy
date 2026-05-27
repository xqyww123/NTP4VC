theory cpumask_copy_Why3_ide_VCcpumask_copy_loop_inv_established_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_should_we_balance_lib.A_thread_variables_properties_A_thread_variables_properties" "frama_c_should_we_balance_lib.Compound_Compound"
begin
theorem goal2:
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift (t_1 (shift a (0 :: int))) (0 :: int); a_3 :: addr = shift (t_1 (shift a_1 (0 :: int))) (0 :: int) in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> valid_rd t a (1 :: int) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rd t a_2 l_size \<longrightarrow> valid_rw t a_3 l_size \<longrightarrow> separated a_3 l_size a_2 l_size \<longrightarrow> (0 :: int) \<le> l_size"
  sorry
end
