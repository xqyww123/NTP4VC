theory linked_n_merge_segment_Why3_ide_VClinked_n_merge_segment_loop_inv_preserved_part2_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "frama_c_contiki_list_lib.Axiomatic_Axiomatic"
begin
theorem goal6:
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes a_3 :: "addr"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_4 :: addr = t_1 (shift (t_1 (shift a_3 (i_2 + i_3 - (1 :: int)))) (0 :: int)) in \<not>i = (0 :: int) \<longrightarrow> (0 :: int) < i_3 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_3 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> (2 :: int) \<le> i_3 \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_sint32 i_3 \<longrightarrow> is_sint32 (i_3 - (1 :: int)) \<longrightarrow> valid_rw t (shift a_3 (0 :: int)) (2147483646 :: int) \<longrightarrow> p_linked_n t t_1 a a_3 i_2 i a_2 \<longrightarrow> p_linked_n t t_1 a_2 a_3 (i + i_2) i_1 a_1 \<longrightarrow> p_linked_n t t_1 a a_3 i_2 i_3 a_4 \<longrightarrow> p_linked_n t t_1 a_4 a_3 (i_2 + i_3) (i + i_1 - i_3) a_1 \<longrightarrow> i_3 \<le> (1 :: int) + i"
  sorry
end
