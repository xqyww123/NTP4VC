theory memchr_Why3_ide_VCmemchr_found_post_part1_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic1_Axiomatic1" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.Axiomatic_Axiomatic"
begin
theorem goal8:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 (shift a i_2); x_1 :: int = i - i_1; a_1 :: addr = shift a x_1; x_2 :: int = t_1 a_1 in \<not>i_1 = (0 :: int) \<longrightarrow> x = to_sint8 i_3 \<longrightarrow> x_2 = x \<longrightarrow> (0 :: int) < i \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> -(128 :: int) \<le> i_3 \<longrightarrow> i_3 \<le> (127 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint32 i_3 \<longrightarrow> valid_rw t (shift a (0 :: int)) i \<longrightarrow> addr_le a a_1 \<longrightarrow> addr_le a_1 (shift a i) \<longrightarrow> is_sint8 x_2 \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 + i_1 < i \<longrightarrow> \<not>x_2 = t_1 (shift a i_4)) \<longrightarrow> p_exists_first_occurence_of_char t t_1 a i_3 x_1"
  sorry
end
