theory array_pop_Why3_ide_VCarray_pop_assert_rte_mem_access_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Axiomatic_Axiomatic"
begin
theorem goal9:
  fixes a_3 :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_4 :: addr = shift a_3 (0 :: int); a_5 :: addr = shift a_3 i_1; x :: int = i + i_2 in (0 :: int) < i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> valid_rw t a_4 (2147483646 :: int) \<longrightarrow> separated a_1 (1 :: int) a_4 (2147483646 :: int) \<longrightarrow> separated (t_1 a_1) (4 :: int) a_4 (2147483646 :: int) \<longrightarrow> p_linked_n t t_1 a a_3 i_2 i a_2 \<longrightarrow> p_linked_n t t_1 (t_1 a_5) a_3 i_1 (i_2 - i_1) a \<longrightarrow> (\<forall>(i_3 :: int). i_1 \<le> i_3 \<longrightarrow> i_3 < x \<longrightarrow> separated a_1 (1 :: int) (t_1 (shift a_3 i_3)) (4 :: int)) \<longrightarrow> (\<forall>(i_3 :: int). i_1 \<le> i_3 \<longrightarrow> i_3 < x \<longrightarrow> separated (t_1 (shift a_3 i_3)) (4 :: int) a_4 (2147483646 :: int)) \<longrightarrow> (\<forall>(i_4 :: int) (i_3 :: int). \<not>i_4 = i_3 \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> i_1 \<le> i_4 \<longrightarrow> i_3 < x \<longrightarrow> i_4 < x \<longrightarrow> \<not>t_1 (shift a_3 i_4) = t_1 (shift a_3 i_3)) \<longrightarrow> (\<forall>(i_4 :: int) (i_3 :: int). \<not>i_4 = i_3 \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> i_1 \<le> i_4 \<longrightarrow> i_3 < x \<longrightarrow> i_4 < x \<longrightarrow> separated (t_1 (shift a_3 i_4)) (4 :: int) (t_1 (shift a_3 i_3)) (4 :: int)) \<longrightarrow> valid_rd t a_5 (1 :: int)"
  sorry
end
