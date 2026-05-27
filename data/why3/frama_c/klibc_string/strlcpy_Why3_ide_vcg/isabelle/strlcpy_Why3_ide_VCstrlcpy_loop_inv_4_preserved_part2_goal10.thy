theory strlcpy_Why3_ide_VCstrlcpy_loop_inv_4_preserved_part2_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.Axiomatic_Axiomatic"
begin
theorem goal10:
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes a_1 :: "addr"
  fixes i_3 :: "int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_3 :: addr = shift a_2 (0 :: int); a_4 :: addr \<Rightarrow> int = havoc t_1 t_2 a_3 i; a_5 :: addr = shift a_1 i_3; a_6 :: int = a_4 a_5; x :: int = offset a_2; x_1 :: int = offset a; x_2 :: int = to_uint32 ((1 :: int) + i_3); x_3 :: int = l_length a_4 a_1; x_4 :: int = (2 :: int) + i_3 in \<not>a_6 = (0 :: int) \<longrightarrow> (0 :: int) < i \<longrightarrow> i \<le> i_1 \<longrightarrow> i \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> x \<le> x_1 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> to_uint32 i \<le> x_2 \<longrightarrow> x_1 \<le> i + x \<longrightarrow> i_3 \<le> x_3 \<longrightarrow> (2 :: int) + x_2 \<le> i \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_sint32 i \<longrightarrow> addr_le a_2 a \<longrightarrow> p_length_of_str_is t t_2 a_1 i_1 \<longrightarrow> p_length_of_str_is t t_2 a_1 i_2 \<longrightarrow> addr_le a (shift a_2 i) \<longrightarrow> addr_le a_1 a_5 \<longrightarrow> valid_rw t a_3 i \<longrightarrow> separated (shift a_1 (0 :: int)) ((1 :: int) + l_length t_2 a_1) a_3 i \<longrightarrow> is_sint8 a_6 \<longrightarrow> addr_le a_5 (shift a_1 x_3) \<longrightarrow> (x_4 \<le> i \<longrightarrow> shift a_2 i_3 = a) \<longrightarrow> (x_4 \<le> i \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < i_3 \<longrightarrow> a_4 (shift a_2 i_4) = a_4 (shift a_1 i_4))) \<longrightarrow> shift a_2 x_2 = a"
  sorry
end
