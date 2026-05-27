theory X__parse_open_mode_Why3_ide_VC__parse_open_mode_loop_inv_3_established_part2_goal22
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Axiomatic_Axiomatic" "frama_c_klibc_stdio_lib.Compound_Compound" "frama_c_klibc_stdio_lib.A_Length_A_Length"
begin
theorem goal22:
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "sconst t_1"
  assumes fact3: "p_length_of_str_is t t_1 a i"
  assumes fact4: "p_length_of_str_is t t_1 a i_1"
  shows "addr_le a (shift a (l_length t_1 a))"
  sorry
end
