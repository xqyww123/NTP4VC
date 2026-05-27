theory memb_init_Why3_ide_VCmemb_init_assert_rte_mem_access_2_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_contiki_memb_lib.Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "frama_c_contiki_memb_lib.Compound_Compound" "frama_c_contiki_memb_lib.A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal2:
  fixes a :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (1 :: int) in region (base a) \<le> (0 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint16 (t_1 a_1) \<longrightarrow> is_uint16 (t_1 (shift a (0 :: int))) \<longrightarrow> p_valid_memb t t_3 t_1 a \<longrightarrow> valid_rd t a_1 (1 :: int)"
  sorry
end
