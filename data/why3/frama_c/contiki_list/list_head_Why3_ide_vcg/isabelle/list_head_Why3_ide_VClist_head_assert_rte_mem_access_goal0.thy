theory list_head_Why3_ide_VClist_head_assert_rte_mem_access_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Axiomatic_Axiomatic" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list"
begin
theorem goal0:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "framed t_1"
  assumes fact3: "linked t"
  assumes fact4: "is_sint32 i"
  assumes fact5: "is_sint32 i_1"
  assumes fact6: "valid_rw t a (1 :: int)"
  assumes fact7: "p_linked_n t t_1 (t_1 a) a_1 i_1 i (Mk_addr (0 :: int) (0 :: int))"
  shows "valid_rd t a (1 :: int)"
  sorry
end
