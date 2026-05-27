theory bsearch_Why3_ide_VCbsearch_assign_exit_part1_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Globals_Globals" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal0:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  assumes fact0: "region (2605 :: int) \<le> (0 :: int)"
  assumes fact1: "region (base a) \<le> (0 :: int)"
  assumes fact2: "region (base a_1) \<le> (0 :: int)"
  assumes fact3: "linked t"
  assumes fact4: "is_uint64 i"
  assumes fact5: "valid_rd t (shift a (0 :: int)) (2 :: int)"
  shows "\<not>valid_rd t (shift a_1 (0 :: int)) ((1 :: int) + i)"
  sorry
end
