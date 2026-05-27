theory memb_inmemb_Why3_ide_VCmemb_inmemb_assert_rte_mem_access_4_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_contiki_memb_lib.Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "frama_c_contiki_memb_lib.Compound_Compound" "frama_c_contiki_memb_lib.A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal2:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int); a_3 :: addr = shift a_1 (3 :: int) in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_uint16 (t_1 (shift a_1 (1 :: int))) \<longrightarrow> is_uint16 (t_1 a_2) \<longrightarrow> p_valid_memb t t_2 t_1 a_1 \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> addr_le (t_2 a_3) a \<longrightarrow> valid_rd t a_2 (1 :: int)"
  sorry
end
