theory cpumask_andnot_Why3_ide_VCcpumask_andnot_loop_inv_established_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_should_we_balance_lib.A_thread_variables_properties_A_thread_variables_properties" "frama_c_should_we_balance_lib.Compound_Compound" "frama_c_should_we_balance_lib.A_schedule_cpumask_A_schedule_cpumask"
begin
theorem goal3:
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_3 :: addr = shift (t_1 (shift a (0 :: int))) (0 :: int); a_4 :: addr = shift (t_1 (shift a_1 (0 :: int))) (0 :: int); a_5 :: addr = shift (t_1 (shift a_2 (0 :: int))) (0 :: int) in \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> valid_rd t a (1 :: int) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t a_3 l_size \<longrightarrow> valid_rd t a_4 l_size \<longrightarrow> valid_rw t a_5 l_size \<longrightarrow> (\<not>a_2 = a \<longrightarrow> separated a_5 l_size a_3 l_size) \<longrightarrow> (\<not>a_2 = a_1 \<longrightarrow> separated a_5 l_size a_4 l_size) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < l_size \<longrightarrow> separated a_5 l_size (shift (t_1 (shift (l_cpu_smt_mask i) (0 :: int))) (0 :: int)) l_size) \<longrightarrow> (0 :: int) \<le> l_size"
  sorry
end
