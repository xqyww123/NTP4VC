theory index_of_existing_item_weak_Why3_ide_VCindex_of_existing_item_weak_post_part2_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "frama_c_contiki_list_lib.A_Index_of_item_A_Index_of_item" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = t_1 (shift a i_2) in a_1 = t_1 (shift a i_1) \<longrightarrow> l_index_of t_1 a_1 a i_3 i = i \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_3 \<le> i \<longrightarrow> i_1 < i \<longrightarrow> i_3 \<le> i_1 \<longrightarrow> i_2 < i \<longrightarrow> i_3 \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_sint32 i_3 \<longrightarrow> valid_rw t (shift a i_3) (i - i_3) \<longrightarrow> \<not>(\<forall>(i_4 :: int). i_4 < i \<longrightarrow> i_3 \<le> i_4 \<longrightarrow> \<not>a_1 = t_1 (shift a i_4))"
  sorry
end
