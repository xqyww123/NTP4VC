theory linked_n_bounds_Why3_ide_VClinked_n_bounds_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Axiomatic_Axiomatic" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list"
begin
theorem goal0:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "region (base a_2) \<le> (0 :: int)"
  assumes fact3: "framed t_1"
  assumes fact4: "linked t"
  assumes fact5: "is_sint32 i"
  assumes fact6: "is_sint32 i_1"
  assumes fact7: "p_linked_n t t_1 a a_2 i_1 i a_1"
  shows "i = (0 :: int) \<and> (0 :: int) \<le> i_1 \<and> i_1 \<le> (2147483646 :: int) \<or> (0 :: int) < i \<and> (0 :: int) \<le> i_1 \<and> i_1 \<le> (2147483645 :: int)"
  sorry
end
