theory memchr_Why3_ide_VCmemchr_loop_inv_4_established_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal9:
  fixes a_3 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a_5 :: "addr"
  fixes a_4 :: "addr"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a_3) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "is_sint32 i_1"
  assumes fact3: "is_uint64 i"
  assumes fact4: "addr_lt a_5 a_4"
  assumes fact5: "addr_le a_2 a_5"
  assumes fact6: "valid_rd t (shift a (0 :: int)) i"
  assumes fact7: "valid_rd t (shift a_1 (0 :: int)) i"
  shows "\<not>t_1 a_5 = to_uint8 i_1"
  sorry
end
