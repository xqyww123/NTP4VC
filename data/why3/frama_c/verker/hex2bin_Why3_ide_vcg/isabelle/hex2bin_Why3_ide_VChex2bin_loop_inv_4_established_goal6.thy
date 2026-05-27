theory hex2bin_Why3_ide_VChex2bin_loop_inv_4_established_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal6:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "sconst t_1"
  assumes fact4: "is_uint64 i"
  assumes fact5: "valid_rw t (shift a_1 (0 :: int)) ((1 :: int) + i)"
  assumes fact6: "valid_rd t (shift a (0 :: int)) ((1 :: int) + (2 :: int) * i)"
  shows "(0 :: int) \<le> i"
  and "addr_le a_1 a_1"
  sorry
end
