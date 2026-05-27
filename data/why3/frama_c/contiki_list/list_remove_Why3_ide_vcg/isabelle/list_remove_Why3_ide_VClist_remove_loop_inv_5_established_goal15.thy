theory list_remove_Why3_ide_VClist_remove_loop_inv_5_established_goal15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "frama_c_contiki_list_lib.Axiomatic_Axiomatic" "frama_c_contiki_list_lib.A_Index_of_item_A_Index_of_item" "frama_c_contiki_list_lib.Axiomatic1_Axiomatic1"
begin
theorem goal15:
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> real"
  shows "let a_3 :: addr = t_2 a; a_4 :: addr = shift a_2 (0 :: int); x :: int = i + i_1 in \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>a_3 = a_1 \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> i \<le> (2147483645 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_4 (2147483646 :: int) \<longrightarrow> separated a (1 :: int) a_4 (2147483646 :: int) \<longrightarrow> separated a_3 (4 :: int) a_4 (2147483646 :: int) \<longrightarrow> p_linked_n t t_2 a_3 a_2 i_1 i (Mk_addr (0 :: int) (0 :: int)) \<longrightarrow> is_sint32 (l_index_of t_2 a_1 a_2 i_1 x) \<longrightarrow> (\<forall>(i_2 :: int). i_1 \<le> i_2 \<longrightarrow> i_2 < x \<longrightarrow> separated a (1 :: int) (t_2 (shift a_2 i_2)) (4 :: int)) \<longrightarrow> (\<forall>(i_2 :: int). i_1 \<le> i_2 \<longrightarrow> i_2 < x \<longrightarrow> separated (t_2 (shift a_2 i_2)) (4 :: int) a_4 (2147483646 :: int)) \<longrightarrow> (\<forall>(i_2 :: int). let a_5 :: addr = t_2 (shift a_2 i_2) in \<not>a_5 = a_1 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i_2 < x \<longrightarrow> separated a_1 (4 :: int) a_5 (4 :: int)) \<longrightarrow> (\<forall>(i_3 :: int) (i_2 :: int). \<not>i_3 = i_2 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> i_2 < x \<longrightarrow> i_3 < x \<longrightarrow> \<not>t_2 (shift a_2 i_3) = t_2 (shift a_2 i_2)) \<longrightarrow> (\<forall>(i_3 :: int) (i_2 :: int). \<not>i_3 = i_2 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> i_2 < x \<longrightarrow> i_3 < x \<longrightarrow> separated (t_2 (shift a_2 i_3)) (4 :: int) (t_2 (shift a_2 i_2)) (4 :: int)) \<longrightarrow> p_unchanged t t_2 t_1 t t_2 t_1 a_2 i_1 i_1"
  sorry
end
