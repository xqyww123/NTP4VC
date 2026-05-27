theory memscan_Why3_ide_VCmemscan_loop_inv_4_established_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal11:
  fixes a_5 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes a_4 :: "addr"
  fixes a_3 :: "addr"
  assumes fact0: "region (base a_5) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "is_uint64 i"
  assumes fact3: "valid_rd t (shift a (0 :: int)) i"
  assumes fact4: "valid_rd t (shift a_1 (0 :: int)) i"
  shows "addr_le a_2 a_4"
  and "addr_le a_4 (shift a_3 i)"
  sorry
end
