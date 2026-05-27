theory fopen_Why3_ide_VCfopen_call___parse_open_mode_pre_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "frama_c_klibc_stdio_lib.Axiomatic_Axiomatic"
begin
theorem goal1:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "framed t_2"
  assumes fact3: "linked t"
  assumes fact4: "sconst t_1"
  assumes fact5: "p_length_of_str_is t t_1 a i"
  assumes fact6: "p_length_of_str_is t t_1 a i_3"
  assumes fact7: "p_length_of_str_is t t_1 a_1 i_1"
  assumes fact8: "p_length_of_str_is t t_1 a_1 i_2"
  shows "\<exists>(i_4 :: int). p_length_of_str_is t t_1 a i_4"
  sorry
end
