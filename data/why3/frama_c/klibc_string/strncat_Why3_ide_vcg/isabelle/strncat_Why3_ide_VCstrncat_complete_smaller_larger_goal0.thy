theory strncat_Why3_ide_VCstrncat_complete_smaller_larger_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length"
begin
theorem goal0:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = l_length t_1 a; a_2 :: addr = shift a_1 (0 :: int); x_1 :: int = (2 :: int) * i; a_3 :: addr = shift a (0 :: int); x_2 :: int = i + x in (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> p_length_of_str_is t t_1 a_1 i_1 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_2 \<longrightarrow> i < x \<and> valid_rw t a_2 x_1 \<and> separated a_3 x_1 a_2 i \<and> (\<exists>(i_3 :: int). (0 :: int) \<le> i_3 \<and> i_3 < i \<and> p_length_of_str_is t t_1 a i_3) \<or> x \<le> i \<and> valid_rw t a_2 x_2 \<and> separated a_3 x_2 a_2 i \<and> (\<exists>(i_3 :: int). (0 :: int) \<le> i_3 \<and> i_3 < i \<and> p_length_of_str_is t t_1 a i_3)"
  sorry
end
