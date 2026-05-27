theory list_chop_Why3_ide_VClist_chop_empty_post_part2_goal44
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "frama_c_contiki_list_lib.Axiomatic_Axiomatic"
begin
theorem goal44:
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  shows "let a_2 :: addr = t_1 a; a_3 :: addr = t_1 (shift a_2 (0 :: int)); a_4 :: addr = shift a_1 (0 :: int) in a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_3 = a_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_4 (2147483646 :: int) \<longrightarrow> separated a (1 :: int) a_4 (2147483646 :: int) \<longrightarrow> separated a_2 (4 :: int) a_4 (2147483646 :: int) \<longrightarrow> \<not>p_linked_n t t_1 a_2 a_1 i (0 :: int) a_3"
  sorry
end
