theory array_push_Why3_ide_VCarray_push_loop_assign_part5_goal45
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Axiomatic_Axiomatic" "frama_c_contiki_list_lib.Axiomatic1_Axiomatic1"
begin
theorem goal45:
  fixes a_4 :: "addr"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes a :: "addr"
  fixes a_3 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> real"
  shows "let a_5 :: addr = shift a_4 ((1 :: int) + i_1 - i_2); x_1 :: int = (1 :: int) + i_2 + i_3; a_6 :: addr \<Rightarrow> addr = havoc t_2 t_3 a_5 x_1; a_7 :: addr = t_3 a_1; x_2 :: int = i_1 + i_3; x_3 :: int = (1 :: int) + i_1; x_4 :: int = (1 :: int) + i_1 + i_3; x_5 :: int = i_1 - i_2; a_8 :: addr = shift a_4 (0 :: int); a_9 :: addr = shift a_4 x_3; x_6 :: int = (2 :: int) + i_1 in \<not>i_2 = (0 :: int) \<longrightarrow> (i_3 = (0 :: int) \<longleftrightarrow> i = (0 :: int)) \<longrightarrow> ((0 :: int) < i_3 \<longleftrightarrow> i = (1 :: int)) \<longrightarrow> \<not>i_2 + i_3 = -(1 :: int) \<longrightarrow> a_6 a_1 = a_7 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> region (base a_4) \<le> (0 :: int) \<longrightarrow> -(1 :: int) \<le> i_2 \<longrightarrow> x_2 \<le> (2147483644 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> is_sint32 x_3 \<longrightarrow> is_sint32 x_4 \<longrightarrow> is_sint32 x_1 \<longrightarrow> is_sint32 x_5 \<longrightarrow> valid_rw t a_8 (2147483646 :: int) \<longrightarrow> separated a_1 (1 :: int) a_8 (2147483646 :: int) \<longrightarrow> separated a_7 (4 :: int) a_8 (2147483646 :: int) \<longrightarrow> \<not>invalid t a_9 (1 :: int) \<longrightarrow> p_linked_n t t_3 a a_4 x_5 x_1 a_3 \<longrightarrow> p_array_swipe_right a_6 t_3 a_4 x_6 ((2 :: int) + i_1 + i_3) \<longrightarrow> p_linked_n t a_6 a a_4 x_5 ((1 :: int) + i_2) a_2 \<longrightarrow> p_linked_n t a_6 a_2 a_4 x_6 i_3 a_3 \<longrightarrow> p_unchanged t a_6 t_1 t t_3 t_1 a_4 x_5 x_3 \<longrightarrow> (\<forall>(i_4 :: int). i_1 \<le> i_4 + i_2 \<longrightarrow> i_4 \<le> x_2 \<longrightarrow> separated a_1 (1 :: int) (t_3 (shift a_4 i_4)) (4 :: int)) \<longrightarrow> (\<forall>(i_4 :: int). i_1 \<le> i_4 + i_2 \<longrightarrow> i_4 \<le> x_2 \<longrightarrow> separated (t_3 (shift a_4 i_4)) (4 :: int) a_8 (2147483646 :: int)) \<longrightarrow> (\<forall>(i_5 :: int) (i_4 :: int). \<not>i_5 = i_4 \<longrightarrow> i_1 \<le> i_4 + i_2 \<longrightarrow> i_1 \<le> i_5 + i_2 \<longrightarrow> i_4 \<le> x_2 \<longrightarrow> i_5 \<le> x_2 \<longrightarrow> \<not>t_3 (shift a_4 i_5) = t_3 (shift a_4 i_4)) \<longrightarrow> (\<forall>(i_5 :: int) (i_4 :: int). \<not>i_5 = i_4 \<longrightarrow> i_1 \<le> i_4 + i_2 \<longrightarrow> i_1 \<le> i_5 + i_2 \<longrightarrow> i_4 \<le> x_2 \<longrightarrow> i_5 \<le> x_2 \<longrightarrow> separated (t_3 (shift a_4 i_5)) (4 :: int) (t_3 (shift a_4 i_4)) (4 :: int)) \<longrightarrow> (\<forall>(i_4 :: int). x_6 \<le> i_4 \<longrightarrow> i_4 \<le> x_4 \<longrightarrow> separated a_1 (1 :: int) (a_6 (shift a_4 i_4)) (4 :: int)) \<longrightarrow> (\<forall>(i_4 :: int). i_1 \<le> i_4 + i_2 \<longrightarrow> i_4 \<le> i + i_1 + i_3 \<longrightarrow> separated (a_6 (shift a_4 i_4)) (4 :: int) a_8 (2147483646 :: int)) \<longrightarrow> included a_9 (1 :: int) a_5 x_1"
  sorry
end
