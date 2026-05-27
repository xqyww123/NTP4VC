theory list_chop_Why3_ide_VClist_chop_post_Unique_part3_goal20
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "frama_c_contiki_list_lib.Axiomatic_Axiomatic"
begin
theorem goal20:
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_4 :: "int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i_1 + i_2; a_2 :: addr = t_1 (shift a_1 x); a_3 :: addr = shift a_2 (0 :: int); a_4 :: addr = t_1 a_3; a_5 :: addr = t_1 (shift a_4 (0 :: int)); a_6 :: addr = t_1 a; x_1 :: int = i + i_1; a_7 :: addr = shift a_1 (0 :: int); m :: addr \<Rightarrow> addr = t_1(a_3 := a_5) in \<not>i_4 = i_3 \<longrightarrow> a_5 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_5 = a_6 \<longrightarrow> \<not>a_5 = t_1 (shift a_6 (0 :: int)) \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> i_1 \<le> i_4 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> (2 :: int) + i_2 \<le> i \<longrightarrow> (2 :: int) + i_3 \<le> x_1 \<longrightarrow> (2 :: int) + i_4 \<le> x_1 \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_7 (2147483646 :: int) \<longrightarrow> separated a (1 :: int) a_7 (2147483646 :: int) \<longrightarrow> separated a_6 (4 :: int) a_7 (2147483646 :: int) \<longrightarrow> valid_rw t a_4 (4 :: int) \<longrightarrow> p_linked_n t t_1 a_6 a_1 i_1 (i - (2 :: int)) (t_1 (shift a_1 (i + i_1 - (2 :: int)))) \<longrightarrow> p_linked_n t t_1 a_6 a_1 i_1 (i - (1 :: int)) (t_1 (shift a_1 (i + i_1 - (1 :: int)))) \<longrightarrow> p_linked_n t t_1 a_6 a_1 i_1 i a_5 \<longrightarrow> p_linked_n t t_1 a_2 a_1 x (i - i_2) a_5 \<longrightarrow> (\<forall>(i_5 :: int). i_1 \<le> i_5 \<longrightarrow> i_5 < x_1 \<longrightarrow> separated a (1 :: int) (t_1 (shift a_1 i_5)) (4 :: int)) \<longrightarrow> (\<forall>(i_5 :: int). i_1 \<le> i_5 \<longrightarrow> i_5 < x_1 \<longrightarrow> separated (t_1 (shift a_1 i_5)) (4 :: int) a_7 (2147483646 :: int)) \<longrightarrow> (\<forall>(i_6 :: int) (i_5 :: int). \<not>i_6 = i_5 \<longrightarrow> i_1 \<le> i_5 \<longrightarrow> i_1 \<le> i_6 \<longrightarrow> i_5 < x_1 \<longrightarrow> i_6 < x_1 \<longrightarrow> \<not>t_1 (shift a_1 i_6) = t_1 (shift a_1 i_5)) \<longrightarrow> (\<forall>(i_6 :: int) (i_5 :: int). \<not>i_6 = i_5 \<longrightarrow> i_1 \<le> i_5 \<longrightarrow> i_1 \<le> i_6 \<longrightarrow> i_5 < x_1 \<longrightarrow> i_6 < x_1 \<longrightarrow> separated (t_1 (shift a_1 i_6)) (4 :: int) (t_1 (shift a_1 i_5)) (4 :: int)) \<longrightarrow> \<not>m (shift a_1 i_4) = m (shift a_1 i_3)"
  sorry
end
