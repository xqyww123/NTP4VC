theory X__strxspn_Why3_ide_VC__strxspn_loop_inv_6_preserved_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length"
begin
theorem goal8:
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes t_4 :: "addr \<Rightarrow> int"
  fixes t_2 :: "int \<Rightarrow> int"
  fixes i_6 :: "int"
  fixes a :: "addr"
  fixes t_3 :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes i_4 :: "int"
  fixes i_3 :: "int"
  fixes i_5 :: "int"
  fixes t_1 :: "int \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 i_1; x :: int = t_4 a_2; x_1 :: int = l_length t_4 a_1; x_2 :: int = (t_2(to_uint8 x := 1 :: int)) i_6 in \<not>x = (0 :: int) \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_6 \<longrightarrow> i_1 \<le> x_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_6 \<le> (255 :: int) \<longrightarrow> linked t_3 \<longrightarrow> sconst t_4 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint8 (t_4 a_1) \<longrightarrow> p_length_of_str_is t_3 t_4 a i_2 \<longrightarrow> p_length_of_str_is t_3 t_4 a i_4 \<longrightarrow> p_length_of_str_is t_3 t_4 a_1 i_3 \<longrightarrow> p_length_of_str_is t_3 t_4 a_1 i_5 \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> is_sint8 x \<longrightarrow> addr_le a_2 (shift a_1 x_1) \<longrightarrow> separated (shift a (0 :: int)) ((1 :: int) + l_length t_4 a) (shift a_1 (0 :: int)) ((1 :: int) + x_1) \<longrightarrow> i = (0 :: int) \<or> i = (1 :: int) \<longrightarrow> (\<forall>(i_7 :: int). (0 :: int) \<le> i_7 \<longrightarrow> i_7 \<le> (255 :: int) \<longrightarrow> t_1 i_7 = (0 :: int)) \<longrightarrow> (\<forall>(i_7 :: int). let x_3 :: int = t_2 i_7 in (0 :: int) \<le> i_7 \<longrightarrow> i_7 \<le> (255 :: int) \<longrightarrow> x_3 = (0 :: int) \<or> x_3 = (1 :: int)) \<longrightarrow> (\<forall>(i_7 :: int). (0 :: int) \<le> i_7 \<longrightarrow> i_7 \<le> (255 :: int) \<longrightarrow> i_7 < (0 :: int) \<or> (256 :: int) \<le> i_7 \<longrightarrow> t_1 i_7 = t i_7) \<longrightarrow> (\<forall>(i_7 :: int). (0 :: int) \<le> i_7 \<longrightarrow> i_7 < i_1 \<longrightarrow> \<not>t_4 (shift a_1 i_7) = (0 :: int)) \<longrightarrow> (\<forall>(i_7 :: int). (0 :: int) \<le> i_7 \<longrightarrow> i_7 < i_1 \<longrightarrow> t_2 (t_4 (shift a_1 i_7)) = (1 :: int)) \<longrightarrow> x_2 = (0 :: int) \<or> x_2 = (1 :: int)"
  sorry
end
