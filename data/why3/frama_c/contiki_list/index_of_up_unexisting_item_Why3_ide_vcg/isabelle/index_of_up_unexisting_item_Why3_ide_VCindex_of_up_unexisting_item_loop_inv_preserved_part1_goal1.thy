theory index_of_up_unexisting_item_Why3_ide_VCindex_of_up_unexisting_item_loop_inv_preserved_part1_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_contiki_list_lib.A_Index_of_item_A_Index_of_item" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "Why3STD.Cint_Cint"
begin
theorem goal1:
  fixes i_1 :: "int"
  fixes t :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_2 :: "int"
  fixes i :: "int"
  shows "let x :: int = (1 :: int) + i_1 in l_index_of t a a_1 i_2 i = i \<longrightarrow> i_1 \<le> i \<longrightarrow> i_2 \<le> i \<longrightarrow> i_1 < i \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_sint32 x \<longrightarrow> (\<forall>(i_3 :: int). i_3 < i_1 \<longrightarrow> i_2 \<le> i_3 \<longrightarrow> \<not>t (shift a_1 i_3) = a) \<longrightarrow> (\<forall>(i_3 :: int). i_3 < i_1 \<longrightarrow> i_2 \<le> i_3 \<longrightarrow> l_index_of t a a_1 i_1 i = i) \<longrightarrow> i_2 \<le> x"
  sorry
end
