theory mismatch_Why3_ide_VCmismatch_loop_inv_equal_established_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_mismatch_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_mismatch_lib.Axiomatic_Axiomatic"
begin
theorem goal3:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "is_uint32 i"
  assumes fact4: "valid_rd t (shift a (0 :: int)) i"
  assumes fact5: "valid_rd t (shift a_1 (0 :: int)) i"
  shows "p_equalranges_1' t_1 t_1 a_1 (0 :: int) a"
  sorry
end
