theory strlcat_Why3_ide_VCstrlcat_call_strlen_pre_part2_goal29
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.A_Length_A_Length"
begin
theorem goal29:
  fixes a_1 :: "addr"
  fixes i_4 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 i_4; a_3 :: addr = shift a_1 (0 :: int); x :: int = (1 :: int) + i + i_1; x_1 :: int = (1 :: int) + i_2 + i_3; a_4 :: addr = shift a (0 :: int) in (0 :: int) < i_4 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i_4 \<longrightarrow> p_length_of_str_is t t_1 a i_1 \<longrightarrow> p_length_of_str_is t t_1 a i_3 \<longrightarrow> p_length_of_str_is t t_1 a_1 i \<longrightarrow> p_length_of_str_is t t_1 a_1 i_2 \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> valid_rw t a_3 x \<longrightarrow> valid_rw t a_3 x_1 \<longrightarrow> separated a_4 ((1 :: int) + i_1) a_3 x \<longrightarrow> separated a_4 ((1 :: int) + i_3) a_3 x_1 \<longrightarrow> addr_le a_2 (shift a_1 (l_length t_1 a_1)) \<longrightarrow> (\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 < i_4 \<longrightarrow> \<not>t_1 (shift a_1 i_5) = (0 :: int)) \<longrightarrow> (\<exists>(i_5 :: int). p_length_of_str_is t t_1 a i_5)"
  sorry
end
