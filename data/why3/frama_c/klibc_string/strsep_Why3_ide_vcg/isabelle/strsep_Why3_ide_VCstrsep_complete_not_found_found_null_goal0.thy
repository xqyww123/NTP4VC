theory strsep_Why3_ide_VCstrsep_complete_not_found_found_null_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.Axiomatic1_Axiomatic1" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  shows "let a_2 :: addr = t_2 a; a_3 :: addr = shift a_1 (0 :: int); x :: int = (1 :: int) + l_length t_1 a_1; a_4 :: addr = shift a_2 (0 :: int); x_1 :: int = l_length t_1 a_2; x_2 :: int = (1 :: int) + x_1 in \<not>a_2 = a \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> p_length_of_str_is t t_1 a_1 i \<longrightarrow> p_length_of_str_is t t_1 a_1 i_1 \<longrightarrow> separated a (1 :: int) a_3 x \<longrightarrow> separated a_2 (1 :: int) a_3 x \<longrightarrow> separated a (1 :: int) a_4 x_2 \<longrightarrow> separated a_4 x_2 a_3 x \<longrightarrow> separated a_2 (1 :: int) a_4 x_2 \<longrightarrow> a_2 = Mk_addr (0 :: int) (0 :: int) \<or> valid_rw t a_2 (1 :: int) \<longrightarrow> a_2 = Mk_addr (0 :: int) (0 :: int) \<or> (\<exists>(i_2 :: int). p_length_of_str_is t t_1 a_2 i_2) \<longrightarrow> a_2 = Mk_addr (0 :: int) (0 :: int) \<or> valid_rw t a_2 (1 :: int) \<and> (\<exists>(i_2 :: int). p_length_of_str_is t t_1 a_1 i_2) \<and> (\<exists>(i_2 :: int). p_length_of_str_is t t_1 a_2 i_2) \<and> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < x_1 \<longrightarrow> \<not>p_char_in_str t_1 a_1 (t_1 (shift a_2 i_2))) \<or> valid_rw t a_2 (1 :: int) \<and> (\<exists>(i_2 :: int). p_length_of_str_is t t_1 a_1 i_2) \<and> (\<exists>(i_2 :: int). p_length_of_str_is t t_1 a_2 i_2) \<and> (\<exists>(i_2 :: int). (0 :: int) \<le> i_2 \<and> i_2 < x_1 \<and> p_char_in_str t_1 a_1 (t_1 (shift a_2 i_2)))"
  sorry
end
