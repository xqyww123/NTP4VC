theory bsearch_Why3_ide_VCbsearch_assign_normal_part2_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Globals_Globals" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal3:
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  assumes fact0: "i < i_2"
  assumes fact1: "region (2605 :: int) \<le> (0 :: int)"
  assumes fact2: "region (base a) \<le> (0 :: int)"
  assumes fact3: "region (base a_1) \<le> (0 :: int)"
  assumes fact4: "linked t"
  assumes fact5: "is_uint64 i"
  assumes fact6: "is_uint64 i_1"
  assumes fact7: "is_uint64 i_2"
  assumes fact8: "valid_rd t (shift a (0 :: int)) (2 :: int)"
  shows "\<not>valid_rd t (shift a_1 (0 :: int)) ((1 :: int) + i_1)"
  sorry
end
