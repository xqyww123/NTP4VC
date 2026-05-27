theory list_pop_Why3_ide_VClist_pop_empty_post_3_part2_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "frama_c_contiki_list_lib.Axiomatic_Axiomatic" "frama_c_contiki_list_lib.Axiomatic1_Axiomatic1"
begin
theorem goal10:
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> real"
  shows "let a_2 :: addr = t_2 a; a_3 :: addr = shift a_1 (0 :: int) in a_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_3 (2147483646 :: int) \<longrightarrow> separated a (1 :: int) a_3 (2147483646 :: int) \<longrightarrow> separated a_2 (4 :: int) a_3 (2147483646 :: int) \<longrightarrow> p_linked_n t t_2 a_2 a_1 i (0 :: int) a_2 \<longrightarrow> p_unchanged t t_2 t_1 t t_2 t_1 a_1 i i"
  sorry
end
