theory linked_n_all_elements_Why3_ide_VClinked_n_all_elements_post_part2_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "frama_c_contiki_list_lib.Axiomatic_Axiomatic"
begin
theorem goal1:
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  assumes fact0: "i \<le> (0 :: int)"
  assumes fact1: "(0 :: int) \<le> i_1"
  assumes fact2: "i_1 \<le> i_2"
  assumes fact3: "i_2 < i + i_1"
  assumes fact4: "region (base a) \<le> (0 :: int)"
  assumes fact5: "region (base a_1) \<le> (0 :: int)"
  assumes fact6: "region (base a_2) \<le> (0 :: int)"
  assumes fact7: "framed t_1"
  assumes fact8: "linked t"
  assumes fact9: "is_sint32 i"
  assumes fact10: "is_sint32 i_1"
  assumes fact11: "valid_rw t (shift a_2 (0 :: int)) (2147483646 :: int)"
  assumes fact12: "p_linked_n t t_1 a a_2 i_1 i a_1"
  shows "p_linked_n t t_1 (t_1 (shift a_2 i_2)) a_2 i_2 (i + i_1 - i_2) a_1"
  sorry
end
