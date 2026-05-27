theory array_push_Why3_ide_VCarray_push_assign_part4_goal46
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Axiomatic_Axiomatic"
begin
theorem goal46:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a_3 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x_1 :: int = i_1 - i; a_4 :: addr = shift a_3 (0 :: int); a_5 :: addr = shift a_3 ((1 :: int) + i_1 - i) in \<not>i = (0 :: int) \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> i_1 \<le> (2147483645 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> is_sint32 x_1 \<longrightarrow> valid_rw t a_4 (2147483646 :: int) \<longrightarrow> separated a_1 (1 :: int) a_4 (2147483646 :: int) \<longrightarrow> separated (t_1 a_1) (4 :: int) a_4 (2147483646 :: int) \<longrightarrow> \<not>invalid t a_5 i \<longrightarrow> p_linked_n t t_1 a a_3 x_1 i a_2 \<longrightarrow> (\<forall>(i_2 :: int). i_2 < i_1 \<longrightarrow> i_1 \<le> i_2 + i \<longrightarrow> separated a_1 (1 :: int) (t_1 (shift a_3 i_2)) (4 :: int)) \<longrightarrow> (\<forall>(i_2 :: int). i_2 < i_1 \<longrightarrow> i_1 \<le> i_2 + i \<longrightarrow> separated (t_1 (shift a_3 i_2)) (4 :: int) a_4 (2147483646 :: int)) \<longrightarrow> (\<forall>(i_3 :: int) (i_2 :: int). \<not>i_3 = i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> i_3 < i_1 \<longrightarrow> i_1 \<le> i_2 + i \<longrightarrow> i_1 \<le> i_3 + i \<longrightarrow> \<not>t_1 (shift a_3 i_3) = t_1 (shift a_3 i_2)) \<longrightarrow> (\<forall>(i_3 :: int) (i_2 :: int). \<not>i_3 = i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> i_3 < i_1 \<longrightarrow> i_1 \<le> i_2 + i \<longrightarrow> i_1 \<le> i_3 + i \<longrightarrow> separated (t_1 (shift a_3 i_3)) (4 :: int) (t_1 (shift a_3 i_2)) (4 :: int)) \<longrightarrow> included a_5 i (shift a_3 x_1) ((1 :: int) + i)"
  sorry
end
