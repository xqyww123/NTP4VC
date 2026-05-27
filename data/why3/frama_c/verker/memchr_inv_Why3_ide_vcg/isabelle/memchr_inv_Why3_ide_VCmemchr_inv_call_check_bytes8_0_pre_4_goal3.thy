theory memchr_inv_Why3_ide_VCmemchr_inv_call_check_bytes8_0_pre_4_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal3:
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t_1 :: "int \<Rightarrow> int"
  fixes a :: "addr"
  assumes fact0: "to_uint32 (int_of_addr a_1 cmod (8 :: int)) = (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "(17 :: int) \<le> i"
  assumes fact3: "linked t"
  assumes fact4: "is_uint64 i"
  assumes fact5: "is_uint64 i_1"
  assumes fact6: "valid_rw t (shift a_1 (0 :: int)) i"
  shows "valid_rd t_1 (shift a (0 :: int)) (to_uint32 (i_1 cmod (8 :: int)))"
  sorry
end
