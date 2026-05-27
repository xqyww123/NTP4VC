theory fputs_Why3_ide_VCfputs_call__fwrite_pre_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Axiomatic_Axiomatic" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.A_Length_A_Length"
begin
theorem goal1:
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes a :: "addr"
  assumes fact0: "region (base a_1) \<le> (0 :: int)"
  assumes fact1: "region (base a_2) \<le> (0 :: int)"
  assumes fact2: "framed t_2"
  assumes fact3: "linked t"
  assumes fact4: "sconst t_1"
  assumes fact5: "is_sint32 (l_length t_1 a_1)"
  assumes fact6: "p_length_of_str_is t t_1 a_1 i"
  shows "shift a (0 :: int) = a_2"
  sorry
end
