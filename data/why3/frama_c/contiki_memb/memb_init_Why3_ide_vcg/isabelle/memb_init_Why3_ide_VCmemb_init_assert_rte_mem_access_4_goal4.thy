theory memb_init_Why3_ide_VCmemb_init_assert_rte_mem_access_4_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_contiki_memb_lib.Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "frama_c_contiki_memb_lib.Compound_Compound" "frama_c_contiki_memb_lib.A_OccArray_A_OccArray" "Why3STD.Cint_Cint" "frama_c_contiki_memb_lib.Axiomatic12_Axiomatic12" "frama_c_contiki_memb_lib.A_MemSet_A_MemSet"
begin
theorem goal4:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_4 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (1 :: int); x :: int = t_1 a_1; a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a (2 :: int); a_4 :: addr = t_4 a_3 in region (base a) \<le> (0 :: int) \<longrightarrow> framed t_4 \<longrightarrow> linked t \<longrightarrow> sconst t_3 \<longrightarrow> is_uint16 x \<longrightarrow> is_uint16 (t_1 a_2) \<longrightarrow> p_valid_memb t t_4 t_1 a \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> p_valid_or_empty t a_4 x \<longrightarrow> l_memset (havoc t_2 t_3 (shift a_4 (0 :: int)) x) a_4 (0 :: int) x = True \<longrightarrow> valid_rd t a_2 (1 :: int)"
  sorry
end
