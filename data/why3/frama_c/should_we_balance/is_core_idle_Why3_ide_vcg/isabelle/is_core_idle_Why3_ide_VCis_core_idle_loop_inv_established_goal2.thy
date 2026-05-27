theory is_core_idle_Why3_ide_VCis_core_idle_loop_inv_established_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_should_we_balance_lib.A_schedule_cpumask_A_schedule_cpumask" "frama_c_should_we_balance_lib.Compound_Compound" "frama_c_should_we_balance_lib.A_thread_variables_properties_A_thread_variables_properties" "Why3STD.Cint_Cint"
begin
theorem goal2:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  assumes fact0: "\<not>l_idle_cpu i_1 = (0 :: int)"
  assumes fact1: "(0 :: int) \<le> i"
  assumes fact2: "i < l_size"
  assumes fact3: "(0 :: int) \<le> i_1"
  assumes fact4: "i_1 < l_size"
  assumes fact5: "region (base a) \<le> (0 :: int)"
  assumes fact6: "framed t_1"
  assumes fact7: "linked t"
  assumes fact8: "is_uint32 i"
  assumes fact9: "is_sint32 i_1"
  assumes fact10: "\<forall>(i_2 :: int). let a_1 :: addr = shift a i_2 in (0 :: int) \<le> i_2 \<longrightarrow> i_2 < l_size \<longrightarrow> valid_rd t a_1 (1 :: int) \<and> valid_rw t (shift (t_1 (shift a_1 (0 :: int))) (0 :: int)) l_size"
  assumes fact11: "\<forall>(a_1 :: addr). let a_2 :: addr = l_sched_group_cpus a_1; a_3 :: addr = shift (t_1 (shift a_2 (0 :: int))) (0 :: int) in valid_rd t a_2 (1 :: int) \<and> valid_rd t a_3 l_size \<and> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < l_size \<longrightarrow> separated a_3 l_size (shift (t_1 (shift (shift a i_2) (0 :: int))) (0 :: int)) l_size)"
  assumes fact12: "\<forall>(a_1 :: addr). let a_2 :: addr = l_sched_group_mask a_1; a_3 :: addr = shift (t_1 (shift a_2 (0 :: int))) (0 :: int) in valid_rd t a_2 (1 :: int) \<and> valid_rd t a_3 l_size \<and> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < l_size \<longrightarrow> separated a_3 l_size (shift (t_1 (shift (shift a i_2) (0 :: int))) (0 :: int)) l_size)"
  assumes fact13: "\<forall>(a_1 :: addr). let a_2 :: addr = l_group_balance_mask a_1; a_3 :: addr = shift (t_1 (shift a_2 (0 :: int))) (0 :: int) in valid_rd t a_2 (1 :: int) \<and> valid_rd t a_3 l_size \<and> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < l_size \<longrightarrow> separated a_3 l_size (shift (t_1 (shift (shift a i_2) (0 :: int))) (0 :: int)) l_size)"
  assumes fact14: "\<forall>(i_2 :: int). let a_1 :: addr = l_cpu_smt_mask i_2; a_2 :: addr = shift (t_1 (shift a_1 (0 :: int))) (0 :: int) in (0 :: int) \<le> i_2 \<longrightarrow> i_2 < l_size \<longrightarrow> valid_rd t a_1 (1 :: int) \<and> valid_rd t a_2 l_size \<and> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < l_size \<longrightarrow> separated a_2 l_size (shift (t_1 (shift (shift a i_3) (0 :: int))) (0 :: int)) l_size)"
  shows "(0 :: int) \<le> l_size"
  sorry
end
