theory strlcat_Why3_ide_VCstrlcat_loop_inv_5_established_part1_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.A_Length_A_Length"
begin
theorem goal11:
  fixes a_1 :: "addr"
  fixes i_5 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i_4 :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 i_5; a_3 :: addr = shift a_1 (0 :: int); x :: int = (1 :: int) + i_1 + i_2; x_1 :: int = (1 :: int) + i_3 + i_4; a_4 :: addr = shift a (0 :: int) in t_1 a_2 = (0 :: int) \<longrightarrow> (0 :: int) < i \<longrightarrow> i_5 \<le> i \<longrightarrow> i_5 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_5 \<longrightarrow> p_length_of_str_is t t_1 a i_2 \<longrightarrow> p_length_of_str_is t t_1 a i_4 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_1 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_3 \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> valid_rw t a_3 x \<longrightarrow> valid_rw t a_3 x_1 \<longrightarrow> separated a_4 ((1 :: int) + i_2) a_3 x \<longrightarrow> separated a_4 ((1 :: int) + i_4) a_3 x_1 \<longrightarrow> addr_le a_2 (shift a_1 (l_length t_1 a_1)) \<longrightarrow> (\<forall>(i_6 :: int). (0 :: int) \<le> i_6 \<longrightarrow> i_6 < i_5 \<longrightarrow> \<not>t_1 (shift a_1 i_6) = (0 :: int)) \<longrightarrow> addr_le a a"
  sorry
end
