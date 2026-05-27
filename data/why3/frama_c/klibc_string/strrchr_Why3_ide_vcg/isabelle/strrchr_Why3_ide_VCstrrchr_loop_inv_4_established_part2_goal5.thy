theory strrchr_Why3_ide_VCstrrchr_loop_inv_4_established_part2_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal5:
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "-(128 :: int) \<le> i_2"
  assumes fact2: "i_2 \<le> (127 :: int)"
  assumes fact3: "linked t"
  assumes fact4: "sconst t_1"
  assumes fact5: "is_sint32 i_2"
  assumes fact6: "p_length_of_str_is t t_1 a i"
  assumes fact7: "p_length_of_str_is t t_1 a i_1"
  shows "addr_le a (shift a (l_length t_1 a))"
  sorry
end
