theory memmove_Why3_ide_VCmemmove_loop_inv_16_established_part1_goal21
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal21:
  fixes i :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "region (base a) \<le> (0 :: int)"
  assumes fact2: "region (base a_1) \<le> (0 :: int)"
  assumes fact3: "linked t"
  assumes fact4: "sconst t_1"
  assumes fact5: "is_uint32 i"
  assumes fact6: "\<not>addr_lt a_1 a"
  assumes fact7: "valid_rw t (shift a (0 :: int)) i"
  assumes fact8: "valid_rw t (shift a_1 (0 :: int)) i"
  shows "addr_le a (shift a i)"
  sorry
end
