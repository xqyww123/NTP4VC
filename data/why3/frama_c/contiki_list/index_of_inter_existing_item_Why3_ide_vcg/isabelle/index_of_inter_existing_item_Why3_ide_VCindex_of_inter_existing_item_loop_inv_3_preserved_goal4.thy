theory index_of_inter_existing_item_Why3_ide_VCindex_of_inter_existing_item_loop_inv_3_preserved_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "frama_c_contiki_list_lib.A_Index_of_item_A_Index_of_item" "Why3STD.Cint_Cint"
begin
theorem goal4:
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_3 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = l_index_of t_1 a a_1 i_3 i; x_1 :: int = (1 :: int) + i_1 in \<not>t_1 (shift a_1 i_1) = a \<longrightarrow> i_1 \<le> i \<longrightarrow> i_3 \<le> i \<longrightarrow> i_1 < i \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> i_3 \<le> i_1 \<longrightarrow> i_3 \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> x < i \<longrightarrow> i_3 \<le> x \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_sint32 i_3 \<longrightarrow> is_sint32 x_1 \<longrightarrow> valid_rw t (shift a_1 i_3) (i - i_3) \<longrightarrow> (\<forall>(i_4 :: int). i_4 < i_1 \<longrightarrow> i_3 \<le> i_4 \<longrightarrow> \<not>t_1 (shift a_1 i_4) = a) \<longrightarrow> (\<forall>(i_4 :: int). i_4 < i_1 \<longrightarrow> i_3 \<le> i_4 \<longrightarrow> x = l_index_of t_1 a a_1 i_1 i) \<longrightarrow> l_index_of t_1 a a_1 x_1 i = x"
  sorry
end
