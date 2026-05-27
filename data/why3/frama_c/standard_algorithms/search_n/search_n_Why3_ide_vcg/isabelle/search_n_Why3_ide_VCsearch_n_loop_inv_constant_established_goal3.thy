theory search_n_Why3_ide_VCsearch_n_loop_inv_constant_established_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_search_n_lib.Compound_Compound" "frama_c_standard_algorithms_search_n_lib.Axiomatic_Axiomatic"
begin
theorem goal3:
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "(0 :: int) < i"
  assumes fact1: "i \<le> i_1"
  assumes fact2: "region (base a) \<le> (0 :: int)"
  assumes fact3: "linked t"
  assumes fact4: "is_uint32 i"
  assumes fact5: "is_uint32 i_1"
  assumes fact6: "is_sint32 i_2"
  assumes fact7: "is_sint32 (t_1 (shift a (-(1 :: int))))"
  assumes fact8: "valid_rd t (shift a (0 :: int)) i_1"
  shows "p_constantrange t_1 a (0 :: int) (0 :: int) i_2"
  sorry
end
