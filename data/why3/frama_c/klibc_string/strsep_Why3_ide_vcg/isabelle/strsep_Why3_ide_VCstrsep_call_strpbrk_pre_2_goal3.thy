theory strsep_Why3_ide_VCstrsep_call_strpbrk_pre_2_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length"
begin
theorem goal3:
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  shows "let a_2 :: addr = t_2 a; a_3 :: addr = shift a_1 (0 :: int); x :: int = (1 :: int) + l_length t_1 a_1; a_4 :: addr = shift a_2 (0 :: int); x_1 :: int = (1 :: int) + l_length t_1 a_2 in \<not>a_2 = a \<longrightarrow> \<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> p_length_of_str_is t t_1 a_1 i_1 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_2 \<longrightarrow> p_length_of_str_is t t_1 a_2 i \<longrightarrow> separated a (1 :: int) a_3 x \<longrightarrow> separated a_2 (1 :: int) a_3 x \<longrightarrow> separated a (1 :: int) a_4 x_1 \<longrightarrow> separated a_4 x_1 a_3 x \<longrightarrow> separated a_2 (1 :: int) a_4 x_1 \<longrightarrow> (\<exists>(i_3 :: int). p_length_of_str_is t t_1 a_1 i_3)"
  sorry
end
