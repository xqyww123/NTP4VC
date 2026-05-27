theory hex2bin_Why3_ide_VChex2bin_loop_inv_6_established_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Ctype_A_Ctype"
begin
theorem goal9:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes a_2 :: "addr"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "sconst t_1"
  assumes fact4: "is_uint64 i"
  assumes fact5: "addr_lt a_2 a"
  assumes fact6: "addr_le a a_2"
  assumes fact7: "valid_rw t (shift a_1 (0 :: int)) ((1 :: int) + i)"
  assumes fact8: "valid_rd t (shift a (0 :: int)) ((1 :: int) + (2 :: int) * i)"
  shows "p_isxdigit (t_1 a_2)"
  sorry
end
