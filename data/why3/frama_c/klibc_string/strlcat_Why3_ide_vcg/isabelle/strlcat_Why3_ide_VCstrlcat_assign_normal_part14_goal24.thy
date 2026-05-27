theory strlcat_Why3_ide_VCstrlcat_assign_normal_part14_goal24
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.A_Length_A_Length"
begin
theorem goal24:
  fixes a_1 :: "addr"
  fixes i_6 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i_4 :: "int"
  fixes i_5 :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 i_6; a_3 :: addr = shift a_1 (0 :: int); x :: int = (1 :: int) + i_2 + i_3; x_1 :: int = (1 :: int) + i_4 + i_5; a_4 :: addr = shift a (0 :: int); x_2 :: int = l_length t_1 a_1 in t_1 a_2 = (0 :: int) \<longrightarrow> (0 :: int) < i \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> i_6 \<le> i \<longrightarrow> i_6 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_6 \<longrightarrow> is_sint32 i_1 \<longrightarrow> p_length_of_str_is t t_1 a i_3 \<longrightarrow> p_length_of_str_is t t_1 a i_5 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_2 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_4 \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> \<not>invalid t a_3 i_1 \<longrightarrow> valid_rw t a_3 x \<longrightarrow> valid_rw t a_3 x_1 \<longrightarrow> separated a_4 ((1 :: int) + i_3) a_3 x \<longrightarrow> separated a_4 ((1 :: int) + i_5) a_3 x_1 \<longrightarrow> addr_le a_2 (shift a_1 x_2) \<longrightarrow> (\<forall>(i_7 :: int). (0 :: int) \<le> i_7 \<longrightarrow> i_7 < i_6 \<longrightarrow> \<not>t_1 (shift a_1 i_7) = (0 :: int)) \<longrightarrow> i_1 \<le> (1 :: int) + l_length t_1 a + x_2"
  sorry
end
