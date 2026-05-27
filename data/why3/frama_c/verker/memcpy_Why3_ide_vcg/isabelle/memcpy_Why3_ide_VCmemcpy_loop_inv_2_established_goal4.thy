theory memcpy_Why3_ide_VCmemcpy_loop_inv_2_established_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal4:
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
  assumes fact5: "valid_rd t (shift a (0 :: int)) i"
  assumes fact6: "valid_rw t (shift a_1 (0 :: int)) i"
  shows "addr_le a_1 a_1"
  and "addr_le a_1 (shift a_1 i)"
  sorry
end
