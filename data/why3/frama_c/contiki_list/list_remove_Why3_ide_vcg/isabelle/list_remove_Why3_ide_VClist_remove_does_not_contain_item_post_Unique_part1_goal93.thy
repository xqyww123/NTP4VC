theory list_remove_Why3_ide_VClist_remove_does_not_contain_item_post_Unique_part1_goal93
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "frama_c_contiki_list_lib.Axiomatic_Axiomatic" "frama_c_contiki_list_lib.A_Index_of_item_A_Index_of_item"
begin
theorem goal93:
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a_2 :: "addr"
  fixes i_3 :: "int"
  fixes i_2 :: "int"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_3 :: addr = t_1 a; x :: int = i + i_1; a_4 :: addr = shift a_2 (0 :: int) in \<not>i_3 = i_2 \<longrightarrow> \<not>a_3 = a_1 \<longrightarrow> a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> i_2 < x \<longrightarrow> i_3 < x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> i \<le> (2147483645 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_4 (2147483646 :: int) \<longrightarrow> separated a (1 :: int) a_4 (2147483646 :: int) \<longrightarrow> separated a_3 (4 :: int) a_4 (2147483646 :: int) \<longrightarrow> p_linked_n t t_1 a_3 a_2 i_1 i a_3 \<longrightarrow> is_sint32 (l_index_of t_1 a_1 a_2 i_1 x) \<longrightarrow> (\<forall>(i_4 :: int). i_1 \<le> i_4 \<longrightarrow> i_4 < x \<longrightarrow> \<not>t_1 (shift a_2 i_4) = a_1) \<longrightarrow> (\<forall>(i_4 :: int). i_1 \<le> i_4 \<longrightarrow> i_4 < x \<longrightarrow> separated a (1 :: int) (t_1 (shift a_2 i_4)) (4 :: int)) \<longrightarrow> (\<forall>(i_4 :: int). i_1 \<le> i_4 \<longrightarrow> i_4 < x \<longrightarrow> separated (t_1 (shift a_2 i_4)) (4 :: int) a_4 (2147483646 :: int)) \<longrightarrow> (\<forall>(i_4 :: int). let a_5 :: addr = t_1 (shift a_2 i_4) in \<not>a_5 = a_1 \<longrightarrow> i_1 \<le> i_4 \<longrightarrow> i_4 < x \<longrightarrow> separated a_1 (4 :: int) a_5 (4 :: int)) \<longrightarrow> (\<forall>(i_5 :: int) (i_4 :: int). \<not>i_5 = i_4 \<longrightarrow> i_1 \<le> i_4 \<longrightarrow> i_1 \<le> i_5 \<longrightarrow> i_4 < x \<longrightarrow> i_5 < x \<longrightarrow> \<not>t_1 (shift a_2 i_5) = t_1 (shift a_2 i_4)) \<longrightarrow> (\<forall>(i_5 :: int) (i_4 :: int). \<not>i_5 = i_4 \<longrightarrow> i_1 \<le> i_4 \<longrightarrow> i_1 \<le> i_5 \<longrightarrow> i_4 < x \<longrightarrow> i_5 < x \<longrightarrow> separated (t_1 (shift a_2 i_5)) (4 :: int) (t_1 (shift a_2 i_4)) (4 :: int)) \<longrightarrow> \<not>t_1 (shift a_2 i_3) = t_1 (shift a_2 i_2)"
  sorry
end
