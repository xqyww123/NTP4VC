theory memscan_Why3_ide_VCmemscan_loop_inv_2_established_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal7:
  fixes a_4 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  assumes fact0: "region (base a_4) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "is_uint64 i"
  assumes fact3: "valid_rd t (shift a (0 :: int)) i"
  assumes fact4: "valid_rd t (shift a_1 (0 :: int)) i"
  shows "offset a_3 = offset a_2"
  sorry
end
