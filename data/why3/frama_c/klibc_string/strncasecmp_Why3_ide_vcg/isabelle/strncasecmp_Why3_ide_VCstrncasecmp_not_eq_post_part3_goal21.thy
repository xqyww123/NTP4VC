theory strncasecmp_Why3_ide_VCstrncasecmp_not_eq_post_part3_goal21
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Axiomatic2_Axiomatic2" "frama_c_klibc_string_lib.A_ToUpper_A_ToUpper"
begin
theorem goal21:
  fixes a :: "addr"
  fixes i :: "int"
  fixes a_1 :: "addr"
  fixes a_6 :: "addr"
  fixes a_7 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_5 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i_4 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes a_2 :: "addr"
  fixes a_4 :: "addr"
  fixes a_3 :: "addr"
  fixes a_5 :: "addr"
  shows "let a_8 :: addr = shift a i; a_9 :: addr = shift a_1 i; a_10 :: addr = shift a_6 (0 :: int); a_11 :: addr = shift a_7 (0 :: int) in \<not>l_toupper (to_uint8 (t_1 (shift a_7 i_5))) = l_toupper (to_uint8 (t_1 (shift a_6 i_5))) \<longrightarrow> (0 :: int) < i \<longrightarrow> (0 :: int) \<le> i_5 \<longrightarrow> i_5 < i \<longrightarrow> region (base a_6) \<le> (0 :: int) \<longrightarrow> region (base a_7) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> p_length_of_str_is t t_1 a_6 i_1 \<longrightarrow> p_length_of_str_is t t_1 a_6 i_4 \<longrightarrow> p_length_of_str_is t t_1 a_7 i_2 \<longrightarrow> p_length_of_str_is t t_1 a_7 i_3 \<longrightarrow> addr_le a_2 a_8 \<longrightarrow> addr_le a_4 a_9 \<longrightarrow> addr_le a_8 (shift a_3 i) \<longrightarrow> addr_le a_9 (shift a_5 i) \<longrightarrow> valid_rw t a_10 i \<longrightarrow> valid_rw t a_11 i \<longrightarrow> separated a_11 i a_10 i \<longrightarrow> \<not>(\<forall>(i_6 :: int). (0 :: int) \<le> i_6 \<longrightarrow> i_6 < i \<longrightarrow> l_toupper (to_uint8 (t_1 (shift a_7 i_6))) = l_toupper (to_uint8 (t_1 (shift a_6 i_6))))"
  sorry
end
