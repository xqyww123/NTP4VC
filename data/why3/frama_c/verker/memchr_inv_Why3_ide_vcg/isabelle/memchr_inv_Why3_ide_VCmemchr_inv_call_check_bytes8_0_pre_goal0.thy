theory memchr_inv_Why3_ide_VCmemchr_inv_call_check_bytes8_0_pre_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal0:
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a :: "addr"
  assumes fact0: "region (base a_1) \<le> (0 :: int)"
  assumes fact1: "i \<le> (16 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "is_uint64 i"
  assumes fact4: "valid_rw t (shift a_1 (0 :: int)) i"
  shows "valid_rd t (shift a (0 :: int)) (to_uint32 i)"
  sorry
end
