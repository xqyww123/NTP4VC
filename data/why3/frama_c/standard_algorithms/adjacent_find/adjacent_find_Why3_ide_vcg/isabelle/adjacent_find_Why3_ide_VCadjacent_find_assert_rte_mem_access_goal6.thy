theory adjacent_find_Why3_ide_VCadjacent_find_assert_rte_mem_access_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_adjacent_find_lib.Compound_Compound" "frama_c_standard_algorithms_adjacent_find_lib.Axiomatic_Axiomatic"
begin
theorem goal6:
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a i_1; x :: int = (1 :: int) + i_1 in (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> i_1 \<le> (4294967294 :: int) \<longrightarrow> (2 :: int) + i_1 \<le> i \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint32 (t_1 a_1) \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> \<not>p_hasequalneighbors t_1 a x \<longrightarrow> is_sint32 (t_1 (shift a x)) \<longrightarrow> valid_rd t a_1 (1 :: int)"
  sorry
end
