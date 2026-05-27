theory array_push_Why3_ide_VCarray_push_post_SubArraySwipeRight_part1_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Axiomatic_Axiomatic" "frama_c_contiki_list_lib.Axiomatic1_Axiomatic1"
begin
theorem goal7:
  fixes a_3 :: "addr"
  fixes i :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_4 :: addr = shift a_3 (0 :: int); x :: int = (1 :: int) + i in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> i \<le> (2147483645 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> valid_rw t a_4 (2147483646 :: int) \<longrightarrow> separated a_1 (1 :: int) a_4 (2147483646 :: int) \<longrightarrow> separated (t_1 a_1) (4 :: int) a_4 (2147483646 :: int) \<longrightarrow> p_linked_n t t_1 a a_3 i (0 :: int) a_2 \<longrightarrow> p_array_swipe_right t_1 t_1 a_3 x x"
  sorry
end
