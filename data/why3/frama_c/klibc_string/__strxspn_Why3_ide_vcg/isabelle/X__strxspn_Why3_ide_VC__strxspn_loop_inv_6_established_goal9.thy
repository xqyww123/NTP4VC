theory X__strxspn_Why3_ide_VC__strxspn_loop_inv_6_established_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length"
begin
theorem goal9:
  fixes t_1 :: "int \<Rightarrow> int"
  fixes i_5 :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_2 :: "int \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes i_2 :: "int"
  fixes i_4 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 i_5 in (0 :: int) \<le> i_5 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_5 \<le> (255 :: int) \<longrightarrow> linked t_2 \<longrightarrow> sconst t_3 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint8 (t_3 a_1) \<longrightarrow> p_length_of_str_is t_2 t_3 a i_1 \<longrightarrow> p_length_of_str_is t_2 t_3 a i_3 \<longrightarrow> p_length_of_str_is t_2 t_3 a_1 i_2 \<longrightarrow> p_length_of_str_is t_2 t_3 a_1 i_4 \<longrightarrow> separated (shift a (0 :: int)) ((1 :: int) + l_length t_3 a) (shift a_1 (0 :: int)) ((1 :: int) + l_length t_3 a_1) \<longrightarrow> i = (0 :: int) \<or> i = (1 :: int) \<longrightarrow> (\<forall>(i_6 :: int). (0 :: int) \<le> i_6 \<longrightarrow> i_6 \<le> (255 :: int) \<longrightarrow> t_1 i_6 = (0 :: int)) \<longrightarrow> (\<forall>(i_6 :: int). (0 :: int) \<le> i_6 \<longrightarrow> i_6 \<le> (255 :: int) \<longrightarrow> i_6 < (0 :: int) \<or> (256 :: int) \<le> i_6 \<longrightarrow> t_1 i_6 = t i_6) \<longrightarrow> x = (0 :: int) \<or> x = (1 :: int)"
  sorry
end
