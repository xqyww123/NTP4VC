theory linked_n_all_elements_Why3_ide_VClinked_n_all_elements_assert_rte_mem_access_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "frama_c_contiki_list_lib.Axiomatic_Axiomatic"
begin
theorem goal8:
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_1 :: "addr"
  shows "let x :: int = i + i_1 in (0 :: int) < i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i_2 < x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> -(2147483648 :: int) \<le> x \<longrightarrow> x \<le> (2147483647 :: int) \<longrightarrow> (2 :: int) + i_2 \<le> x \<longrightarrow> -(2147483647 :: int) \<le> to_sint32 x \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> valid_rw t (shift a_3 (0 :: int)) (2147483646 :: int) \<longrightarrow> p_linked_n t t_1 a a_3 i_1 i a_2 \<longrightarrow> p_linked_n t t_1 a_1 a_3 i_2 (i + i_1 - i_2) a_2 \<longrightarrow> (\<forall>(i_3 :: int). i_1 \<le> i_3 \<longrightarrow> i_3 < i_2 \<longrightarrow> p_linked_n t t_1 (t_1 (shift a_3 i_3)) a_3 i_3 (i + i_1 - i_3) a_2) \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) (1 :: int)"
  sorry
end
