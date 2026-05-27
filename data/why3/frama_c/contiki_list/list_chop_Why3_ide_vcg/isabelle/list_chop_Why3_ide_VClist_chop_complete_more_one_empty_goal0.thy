theory list_chop_Why3_ide_VClist_chop_complete_more_one_empty_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "frama_c_contiki_list_lib.Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int); a_3 :: addr = t_1 a; x :: int = i + i_1 in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_2 (2147483646 :: int) \<longrightarrow> separated a (1 :: int) a_2 (2147483646 :: int) \<longrightarrow> separated a_3 (4 :: int) a_2 (2147483646 :: int) \<longrightarrow> p_linked_n t t_1 a_3 a_1 i_1 i (Mk_addr (0 :: int) (0 :: int)) \<longrightarrow> (\<forall>(i_2 :: int). i_1 \<le> i_2 \<longrightarrow> i_2 < x \<longrightarrow> separated a (1 :: int) (t_1 (shift a_1 i_2)) (4 :: int)) \<longrightarrow> (\<forall>(i_2 :: int). i_1 \<le> i_2 \<longrightarrow> i_2 < x \<longrightarrow> separated (t_1 (shift a_1 i_2)) (4 :: int) a_2 (2147483646 :: int)) \<longrightarrow> (\<forall>(i_3 :: int) (i_2 :: int). \<not>i_3 = i_2 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> i_2 < x \<longrightarrow> i_3 < x \<longrightarrow> \<not>t_1 (shift a_1 i_3) = t_1 (shift a_1 i_2)) \<longrightarrow> (\<forall>(i_3 :: int) (i_2 :: int). \<not>i_3 = i_2 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> i_2 < x \<longrightarrow> i_3 < x \<longrightarrow> separated (t_1 (shift a_1 i_3)) (4 :: int) (t_1 (shift a_1 i_2)) (4 :: int)) \<longrightarrow> i = (0 :: int) \<or> i = (1 :: int) \<or> (2 :: int) \<le> i"
  sorry
end
