theory insertion_sort_Why3_ide_VCinsertion_sort_assert_rte_mem_access_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_insertion_sort_lib.Compound_Compound" "frama_c_standard_algorithms_insertion_sort_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_insertion_sort_lib.A_Count_A_Count" "frama_c_standard_algorithms_insertion_sort_lib.Axiomatic_Axiomatic"
begin
theorem goal10:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); a_2 :: addr \<Rightarrow> int = havoc t_1 t_2 a_1 i in i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rw t a_1 i \<longrightarrow> p_sorted_1' a_2 a (0 :: int) i_1 \<longrightarrow> p_unchanged_1' a_2 t_2 a i_1 i \<longrightarrow> p_multisetunchanged_1' a_2 t_2 a (0 :: int) i_1 \<longrightarrow> valid_rd t (shift a i_1) (1 :: int)"
  sorry
end
