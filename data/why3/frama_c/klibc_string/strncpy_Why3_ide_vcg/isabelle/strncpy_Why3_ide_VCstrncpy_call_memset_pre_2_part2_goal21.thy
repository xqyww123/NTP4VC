theory strncpy_Why3_ide_VCstrncpy_call_memset_pre_2_part2_goal21
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic"
begin
theorem goal21:
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  shows "let a_2 :: addr = shift a_1 (0 :: int); x :: int = -i; a_3 :: addr = shift a x; a_4 :: addr = shift a_1 x in (0 :: int) \<le> i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint8 i_3 \<longrightarrow> is_uint32 i \<longrightarrow> p_length_of_str_is t t_1 a i_1 \<longrightarrow> p_length_of_str_is t t_1 a i_2 \<longrightarrow> valid_rw t a_2 i \<longrightarrow> addr_le a a_3 \<longrightarrow> addr_le a_1 a_4 \<longrightarrow> addr_le a_3 (shift a i) \<longrightarrow> addr_le a_4 (shift a_1 i) \<longrightarrow> separated (shift a (0 :: int)) i a_2 i \<longrightarrow> (\<not>i = (0 :: int) \<longrightarrow> \<not>i_3 = (0 :: int)) \<longrightarrow> valid_rw t a_4 (0 :: int)"
  sorry
end
