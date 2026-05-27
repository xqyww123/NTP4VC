theory array_push_Why3_ide_VCarray_push_loop_inv_UnchangedLeft_preserved_part1_goal31
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Axiomatic_Axiomatic" "frama_c_contiki_list_lib.Axiomatic1_Axiomatic1"
begin
theorem goal31:
  fixes a_4 :: "addr"
  fixes i_2 :: "int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes i_1 :: "int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes a :: "addr"
  fixes a_3 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> real"
  shows "let a_5 :: addr = shift a_4 i_2; a_6 :: addr \<Rightarrow> addr = havoc t_2 t_3 a_5 i_1; a_7 :: addr = t_3 a_1; x :: int = i_1 + i_2; x_1 :: int = i_2 - (1 :: int); a_8 :: addr = shift a_4 (0 :: int); x_2 :: int = (1 :: int) + i_2 in \<not>i_1 = (0 :: int) \<longrightarrow> (i_1 = (1 :: int) \<longleftrightarrow> i = (0 :: int)) \<longrightarrow> ((2 :: int) \<le> i_1 \<longleftrightarrow> i = (1 :: int)) \<longrightarrow> a_6 a_1 = a_7 \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> region (base a_4) \<le> (0 :: int) \<longrightarrow> x \<le> (2147483646 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> is_sint32 x_1 \<longrightarrow> is_sint32 (i_1 + i_2 - (1 :: int)) \<longrightarrow> valid_rw t a_8 (2147483646 :: int) \<longrightarrow> separated a_1 (1 :: int) a_8 (2147483646 :: int) \<longrightarrow> separated a_7 (4 :: int) a_8 (2147483646 :: int) \<longrightarrow> p_linked_n t t_3 a a_4 x_1 i_1 a_3 \<longrightarrow> p_array_swipe_right a_6 t_3 a_4 x_2 x \<longrightarrow> p_linked_n t a_6 a a_4 x_1 (1 :: int) a_2 \<longrightarrow> p_linked_n t a_6 a_2 a_4 x_2 (i_1 - (1 :: int)) a_3 \<longrightarrow> p_unchanged t a_6 t_1 t t_3 t_1 a_4 x_1 i_2 \<longrightarrow> (\<forall>(i_3 :: int). i_2 \<le> (1 :: int) + i_3 \<longrightarrow> (2 :: int) + i_3 \<le> x \<longrightarrow> separated a_1 (1 :: int) (t_3 (shift a_4 i_3)) (4 :: int)) \<longrightarrow> (\<forall>(i_3 :: int). i_2 \<le> (1 :: int) + i_3 \<longrightarrow> (2 :: int) + i_3 \<le> x \<longrightarrow> separated (t_3 (shift a_4 i_3)) (4 :: int) a_8 (2147483646 :: int)) \<longrightarrow> (\<forall>(i_4 :: int) (i_3 :: int). \<not>i_4 = i_3 \<longrightarrow> i_2 \<le> (1 :: int) + i_3 \<longrightarrow> i_2 \<le> (1 :: int) + i_4 \<longrightarrow> (2 :: int) + i_3 \<le> x \<longrightarrow> (2 :: int) + i_4 \<le> x \<longrightarrow> \<not>t_3 (shift a_4 i_4) = t_3 (shift a_4 i_3)) \<longrightarrow> (\<forall>(i_3 :: int). i_2 < i_3 \<longrightarrow> i_3 < x \<longrightarrow> separated a_1 (1 :: int) (a_6 (shift a_4 i_3)) (4 :: int)) \<longrightarrow> (\<forall>(i_3 :: int). i_2 \<le> (1 :: int) + i_3 \<longrightarrow> (2 :: int) + i_3 \<le> i + i_1 + i_2 \<longrightarrow> separated (a_6 (shift a_4 i_3)) (4 :: int) a_8 (2147483646 :: int)) \<longrightarrow> (\<forall>(i_4 :: int) (i_3 :: int). \<not>i_4 = i_3 \<longrightarrow> i_2 \<le> (1 :: int) + i_3 \<longrightarrow> i_2 \<le> (1 :: int) + i_4 \<longrightarrow> (2 :: int) + i_3 \<le> x \<longrightarrow> (2 :: int) + i_4 \<le> x \<longrightarrow> separated (t_3 (shift a_4 i_4)) (4 :: int) (t_3 (shift a_4 i_3)) (4 :: int)) \<longrightarrow> p_unchanged t (a_6(a_5 := a_6 (shift a_4 x_1))) t_1 t t_3 t_1 a_4 x_1 x_1"
  sorry
end
