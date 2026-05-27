theory array_pop_Why3_ide_VCarray_pop_loop_assign_part2_goal31
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Axiomatic_Axiomatic" "frama_c_contiki_list_lib.Axiomatic1_Axiomatic1"
begin
theorem goal31:
  fixes a_4 :: "addr"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes a_1 :: "addr"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes a_3 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> real"
  shows "let a_5 :: addr = shift a_4 i_2; x :: int = i - (1 :: int); a_6 :: addr \<Rightarrow> addr = havoc t_2 t_3 a_5 x; a_7 :: addr = t_3 a_1; x_1 :: int = i + i_2; a_8 :: addr = shift a_4 (0 :: int); a_9 :: addr = shift a_4 i_3; a_10 :: addr = t_3 (shift a_4 i_1); x_2 :: int = i_2 - i_1 in a_6 a_1 = a_7 \<longrightarrow> (0 :: int) < i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i_2 \<le> i_3 \<longrightarrow> i_3 < x_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> region (base a_4) \<le> (0 :: int) \<longrightarrow> (2 :: int) + i_3 \<le> x_1 \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_sint32 i_3 \<longrightarrow> valid_rw t a_8 (2147483646 :: int) \<longrightarrow> \<not>invalid t a_9 (1 :: int) \<longrightarrow> separated a_1 (1 :: int) a_8 (2147483646 :: int) \<longrightarrow> separated a_7 (4 :: int) a_8 (2147483646 :: int) \<longrightarrow> p_linked_n t t_3 a a_4 i_2 i a_3 \<longrightarrow> p_linked_n t t_3 a_10 a_4 i_1 x_2 a \<longrightarrow> p_array_swipe_left a_6 t_3 a_4 i_2 i_3 \<longrightarrow> p_linked_n t a_6 a_2 a_4 ((1 :: int) + i_3) (i + i_2 - (1 :: int) - i_3) a_3 \<longrightarrow> p_linked_n t a_6 a_10 a_4 i_1 x_2 a \<longrightarrow> p_linked_n t a_6 (a_6 (shift a (0 :: int))) a_4 i_2 (i_3 - i_2) a_2 \<longrightarrow> p_unchanged t a_6 t_1 t t_3 t_1 a_4 i_1 i_2 \<longrightarrow> p_unchanged t a_6 t_1 t t_3 t_1 a_4 i_3 x_1 \<longrightarrow> (\<forall>(i_4 :: int). i_1 \<le> i_4 \<longrightarrow> i_4 < x_1 \<longrightarrow> separated a_1 (1 :: int) (t_3 (shift a_4 i_4)) (4 :: int)) \<longrightarrow> (\<forall>(i_4 :: int). i_1 \<le> i_4 \<longrightarrow> i_4 < x_1 \<longrightarrow> separated (t_3 (shift a_4 i_4)) (4 :: int) a_8 (2147483646 :: int)) \<longrightarrow> (\<forall>(i_5 :: int) (i_4 :: int). \<not>i_5 = i_4 \<longrightarrow> i_1 \<le> i_4 \<longrightarrow> i_1 \<le> i_5 \<longrightarrow> i_4 < x_1 \<longrightarrow> i_5 < x_1 \<longrightarrow> \<not>t_3 (shift a_4 i_5) = t_3 (shift a_4 i_4)) \<longrightarrow> (\<forall>(i_5 :: int) (i_4 :: int). \<not>i_5 = i_4 \<longrightarrow> i_1 \<le> i_4 \<longrightarrow> i_1 \<le> i_5 \<longrightarrow> i_4 < x_1 \<longrightarrow> i_5 < x_1 \<longrightarrow> separated (t_3 (shift a_4 i_5)) (4 :: int) (t_3 (shift a_4 i_4)) (4 :: int)) \<longrightarrow> included a_9 (1 :: int) a_5 x"
  sorry
end
