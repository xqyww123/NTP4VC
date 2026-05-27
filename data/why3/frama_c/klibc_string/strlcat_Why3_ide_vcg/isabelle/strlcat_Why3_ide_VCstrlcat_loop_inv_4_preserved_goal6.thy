theory strlcat_Why3_ide_VCstrlcat_loop_inv_4_preserved_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.A_Length_A_Length"
begin
theorem goal6:
  fixes a_1 :: "addr"
  fixes i_6 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i_4 :: "int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_5 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 i_6; x :: int = t_1 a_2; a_3 :: addr = shift a_1 (0 :: int); x_1 :: int = (1 :: int) + i_1 + i_2; x_2 :: int = (1 :: int) + i_3 + i_4; a_4 :: addr = shift a (0 :: int) in \<not>x = (0 :: int) \<longrightarrow> (0 :: int) < i \<longrightarrow> i_6 \<le> i \<longrightarrow> (0 :: int) \<le> i_5 \<longrightarrow> i_6 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_5 < to_uint32 ((1 :: int) + i_6) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_6 \<longrightarrow> p_length_of_str_is t t_1 a i_2 \<longrightarrow> p_length_of_str_is t t_1 a i_4 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_1 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_3 \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> is_sint8 x \<longrightarrow> valid_rw t a_3 x_1 \<longrightarrow> valid_rw t a_3 x_2 \<longrightarrow> separated a_4 ((1 :: int) + i_2) a_3 x_1 \<longrightarrow> separated a_4 ((1 :: int) + i_4) a_3 x_2 \<longrightarrow> addr_le a_2 (shift a_1 (l_length t_1 a_1)) \<longrightarrow> (\<forall>(i_7 :: int). (0 :: int) \<le> i_7 \<longrightarrow> i_7 < i_6 \<longrightarrow> \<not>t_1 (shift a_1 i_7) = (0 :: int)) \<longrightarrow> \<not>t_1 (shift a_1 i_5) = (0 :: int)"
  sorry
end
