theory memb_inmemb_Why3_ide_VCmemb_inmemb_assert_rte_mem_access_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_contiki_memb_lib.Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "frama_c_contiki_memb_lib.Compound_Compound" "frama_c_contiki_memb_lib.A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "framed t_2"
  assumes fact3: "linked t"
  assumes fact4: "is_uint16 (t_1 (shift a_1 (1 :: int)))"
  assumes fact5: "is_uint16 (t_1 (shift a_1 (0 :: int)))"
  assumes fact6: "p_valid_memb t t_2 t_1 a_1"
  shows "valid_rd t (shift a_1 (3 :: int)) (1 :: int)"
  sorry
end
