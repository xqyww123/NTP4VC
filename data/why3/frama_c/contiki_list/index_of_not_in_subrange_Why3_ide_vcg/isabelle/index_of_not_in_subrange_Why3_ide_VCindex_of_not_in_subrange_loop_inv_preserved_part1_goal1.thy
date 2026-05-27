theory index_of_not_in_subrange_Why3_ide_VCindex_of_not_in_subrange_loop_inv_preserved_part1_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "frama_c_contiki_list_lib.A_Index_of_item_A_Index_of_item"
begin
theorem goal1:
  fixes i_2 :: "int"
  fixes t :: "addr \<Rightarrow> addr"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  shows "let x :: int = (1 :: int) + i_2 in \<not>t (shift a_1 i_2) = a \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> i_3 \<le> i_1 \<longrightarrow> i_2 < i_1 \<longrightarrow> i_3 \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_sint32 i_3 \<longrightarrow> is_sint32 x \<longrightarrow> (\<forall>(i_4 :: int). i_4 < i_1 \<longrightarrow> i_3 \<le> i_4 \<longrightarrow> \<not>t (shift a_1 i_4) = a) \<longrightarrow> (\<forall>(i_4 :: int). i_4 < i_2 \<longrightarrow> i_3 \<le> i_4 \<longrightarrow> l_index_of t a a_1 i_3 i = l_index_of t a a_1 i_2 i) \<longrightarrow> i_3 \<le> x"
  sorry
end
