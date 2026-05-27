theory index_of_up_unexisting_item_Why3_ide_VCindex_of_up_unexisting_item_loop_inv_2_preserved_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_contiki_list_lib.A_Index_of_item_A_Index_of_item" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "Why3STD.Cint_Cint"
begin
theorem goal2:
  fixes t :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  shows "let a_1 :: addr = t (shift a i_2) in l_index_of t a_1 a i_3 i = i \<longrightarrow> i_1 \<le> i \<longrightarrow> i_3 \<le> i \<longrightarrow> i_1 < i \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> i_3 \<le> i_1 \<longrightarrow> i_3 \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_sint32 i_3 \<longrightarrow> is_sint32 ((1 :: int) + i_1) \<longrightarrow> (\<forall>(i_4 :: int). i_4 < i_1 \<longrightarrow> i_3 \<le> i_4 \<longrightarrow> \<not>a_1 = t (shift a i_4)) \<longrightarrow> \<not>(\<forall>(i_4 :: int). i_4 < i_1 \<longrightarrow> i_3 \<le> i_4 \<longrightarrow> l_index_of t a_1 a i_1 i = i)"
  sorry
end
