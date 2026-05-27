theory strncmp_Why3_ide_VCstrncmp_disjoint_zero_s2_smaller_s1_smaller_s1_s2_smaller____24_goal24
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.Axiomatic_Axiomatic"
begin
theorem goal24:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a_1 (0 :: int) in (0 :: int) \<le> i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> valid_rw t a_2 i \<longrightarrow> valid_rw t a_3 i \<longrightarrow> separated a_3 i a_2 i \<longrightarrow> (\<exists>(i_1 :: int). \<not>t_1 (shift a_1 i_1) = t_1 (shift a i_1) \<and> (0 :: int) \<le> i_1 \<and> i_1 < i) \<or> (\<exists>(i_1 :: int). t_1 (shift a i_1) = (0 :: int) \<and> (0 :: int) \<le> i_1 \<and> i_1 < i) \<or> (\<exists>(i_1 :: int). t_1 (shift a_1 i_1) = (0 :: int) \<and> (0 :: int) \<le> i_1 \<and> i_1 < i) \<or> (\<forall>(i_1 :: int). i_1 < (0 :: int) \<or> i \<le> i_1 \<or> \<not>p_length_of_str_is t t_1 a i_1 \<or> \<not>p_length_of_str_is t t_1 a_1 i_1 \<or> (\<exists>(i_2 :: int). \<not>t_1 (shift a_1 i_2) = t_1 (shift a i_2) \<and> (0 :: int) \<le> i_2 \<and> i_2 < i_1))"
  sorry
end
