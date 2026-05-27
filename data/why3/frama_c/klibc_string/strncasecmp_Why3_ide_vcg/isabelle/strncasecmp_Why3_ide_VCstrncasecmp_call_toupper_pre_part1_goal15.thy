theory strncasecmp_Why3_ide_VCstrncasecmp_call_toupper_pre_part1_goal15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Axiomatic2_Axiomatic2" "frama_c_klibc_string_lib.A_ToUpper_A_ToUpper"
begin
theorem goal15:
  fixes a_6 :: "addr"
  fixes a_7 :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i_5 :: "int"
  fixes i_3 :: "int"
  fixes i_4 :: "int"
  fixes a_2 :: "addr"
  fixes a_4 :: "addr"
  fixes a_3 :: "addr"
  fixes a_5 :: "addr"
  shows "let a_8 :: addr = shift a_6 (0 :: int); a_9 :: addr = shift a_7 (0 :: int); x :: int = i_1 - i; a_10 :: addr = shift a x; a_11 :: addr = shift a_1 x; x_1 :: int = t_1 a_11 in \<not>i = (0 :: int) \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i \<le> i_1 \<longrightarrow> region (base a_6) \<le> (0 :: int) \<longrightarrow> region (base a_7) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> p_length_of_str_is t t_2 a_6 i_2 \<longrightarrow> p_length_of_str_is t t_2 a_6 i_5 \<longrightarrow> p_length_of_str_is t t_2 a_7 i_3 \<longrightarrow> p_length_of_str_is t t_2 a_7 i_4 \<longrightarrow> valid_rw t a_8 i_1 \<longrightarrow> valid_rw t a_9 i_1 \<longrightarrow> separated a_9 i_1 a_8 i_1 \<longrightarrow> addr_le a_2 a_10 \<longrightarrow> addr_le a_4 a_11 \<longrightarrow> addr_le a_10 (shift a_3 i_1) \<longrightarrow> addr_le a_11 (shift a_5 i_1) \<longrightarrow> is_uint8 x_1 \<longrightarrow> (\<forall>(i_6 :: int). (0 :: int) \<le> i_6 \<longrightarrow> i_6 + i < i_1 \<longrightarrow> l_toupper (to_uint8 (t_2 (shift a_7 i_6))) = l_toupper (to_uint8 (t_2 (shift a_6 i_6)))) \<longrightarrow> (0 :: int) \<le> x_1"
  sorry
end
