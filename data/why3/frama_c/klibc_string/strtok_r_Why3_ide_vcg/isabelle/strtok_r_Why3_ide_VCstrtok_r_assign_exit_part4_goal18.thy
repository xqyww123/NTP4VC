theory strtok_r_Why3_ide_VCstrtok_r_assign_exit_part4_goal18
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length"
begin
theorem goal18:
  fixes t_5 :: "addr \<Rightarrow> addr"
  fixes a_3 :: "addr"
  fixes a_1 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_4 :: "addr"
  fixes a_5 :: "addr"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes t_4 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes a :: "addr"
  shows "let a_6 :: addr = t_5 a_3; a_7 :: addr = shift a_1 (0 :: int); x :: int = (1 :: int) + l_length t_2 a_1; a_8 :: addr = shift a_4 (0 :: int); x_1 :: int = (1 :: int) + l_length t_2 a_4; a_9 :: addr = shift a_5 (0 :: int); x_2 :: int = (1 :: int) + l_length t_3 a_5; a_10 :: addr = shift a_6 (0 :: int); x_3 :: int = (1 :: int) + l_length t_3 a_6; a_11 :: addr = shift a_1 (l_length t_3 a_1) in \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>a_6 = a_3 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_4) \<le> (0 :: int) \<longrightarrow> framed t_4 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> valid_rw t_1 a_3 (1 :: int) \<longrightarrow> valid_rw t (t_4 a_2) (1 :: int) \<longrightarrow> p_length_of_str_is t t_2 a_1 i \<longrightarrow> p_length_of_str_is t t_2 a_4 i_1 \<longrightarrow> p_length_of_str_is t t_2 a_4 i_2 \<longrightarrow> p_length_of_str_is t_1 t_3 a_5 i_3 \<longrightarrow> separated a_2 (1 :: int) a_7 x \<longrightarrow> separated a_2 (1 :: int) a_8 x_1 \<longrightarrow> separated a_3 (1 :: int) a_9 x_2 \<longrightarrow> separated a_7 x a_8 x_1 \<longrightarrow> separated a_6 (1 :: int) a_9 x_2 \<longrightarrow> separated a_3 (1 :: int) a_10 x_3 \<longrightarrow> separated a_10 x_3 a_9 x_2 \<longrightarrow> separated a_6 (1 :: int) a_10 x_3 \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> base a_6 = base a) \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> addr_le a_1 a \<and> addr_le a a_11) \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> addr_le a_1 a_6 \<and> addr_le a_6 a_11) \<longrightarrow> a_6 = Mk_addr (0 :: int) (0 :: int) \<or> valid_rw t_1 a_6 (1 :: int) \<longrightarrow> \<not>(a_6 = Mk_addr (0 :: int) (0 :: int) \<or> (\<exists>(i_4 :: int). p_length_of_str_is t_1 t_3 a_6 i_4))"
  sorry
end
