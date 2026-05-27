theory linked_n_before_last_Why3_ide_VClinked_n_before_last_assert_rte_signed_overflow_3_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "frama_c_contiki_list_lib.Axiomatic_Axiomatic"
begin
theorem goal4:
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  assumes fact0: "(0 :: int) < i"
  assumes fact1: "(0 :: int) \<le> i_1"
  assumes fact2: "region (base a) \<le> (0 :: int)"
  assumes fact3: "region (base a_1) \<le> (0 :: int)"
  assumes fact4: "region (base a_2) \<le> (0 :: int)"
  assumes fact5: "framed t_1"
  assumes fact6: "linked t"
  assumes fact7: "is_sint32 i"
  assumes fact8: "is_sint32 i_1"
  assumes fact9: "valid_rw t (shift a_2 (0 :: int)) (2147483646 :: int)"
  assumes fact10: "p_linked_n t t_1 a a_2 i_1 i a_1"
  shows "-(2147483647 :: int) \<le> to_sint32 (i + i_1)"
  sorry
end
