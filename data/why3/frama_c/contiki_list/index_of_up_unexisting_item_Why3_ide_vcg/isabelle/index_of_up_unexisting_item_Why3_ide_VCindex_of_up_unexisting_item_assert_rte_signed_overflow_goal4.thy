theory index_of_up_unexisting_item_Why3_ide_VCindex_of_up_unexisting_item_assert_rte_signed_overflow_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_contiki_list_lib.A_Index_of_item_A_Index_of_item" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "Why3STD.Cint_Cint"
begin
theorem goal4:
  fixes t :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  assumes fact0: "l_index_of t a a_1 i_2 i = i"
  assumes fact1: "i_1 \<le> i"
  assumes fact2: "i_2 \<le> i"
  assumes fact3: "i_1 < i"
  assumes fact4: "i_2 \<le> i_1"
  assumes fact5: "(0 :: int) \<le> i_2"
  assumes fact6: "region (base a) \<le> (0 :: int)"
  assumes fact7: "region (base a_1) \<le> (0 :: int)"
  assumes fact8: "framed t"
  assumes fact9: "is_sint32 i"
  assumes fact10: "is_sint32 i_1"
  assumes fact11: "is_sint32 i_2"
  assumes fact12: "\<forall>(i_3 :: int). i_3 < i_1 \<longrightarrow> i_2 \<le> i_3 \<longrightarrow> \<not>t (shift a_1 i_3) = a"
  assumes fact13: "\<forall>(i_3 :: int). i_3 < i_1 \<longrightarrow> i_2 \<le> i_3 \<longrightarrow> l_index_of t a a_1 i_1 i = i"
  shows "i_1 \<le> (2147483646 :: int)"
  sorry
end
