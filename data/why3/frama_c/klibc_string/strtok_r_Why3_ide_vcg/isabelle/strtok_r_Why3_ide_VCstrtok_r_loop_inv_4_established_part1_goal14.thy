theory strtok_r_Why3_ide_VCstrtok_r_loop_inv_4_established_part1_goal14
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length"
begin
theorem goal14:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a_1 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  shows "let a_3 :: addr = shift a (0 :: int); x :: int = (1 :: int) + l_length t_1 a; a_4 :: addr = shift a_2 (0 :: int); x_1 :: int = (1 :: int) + l_length t_1 a_2 in \<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> valid_rw t (t_2 a_1) (1 :: int) \<longrightarrow> p_length_of_str_is t t_1 a i \<longrightarrow> p_length_of_str_is t t_1 a_2 i_1 \<longrightarrow> p_length_of_str_is t t_1 a_2 i_2 \<longrightarrow> separated a_1 (1 :: int) a_3 x \<longrightarrow> separated a_1 (1 :: int) a_4 x_1 \<longrightarrow> separated a_3 x a_4 x_1 \<longrightarrow> addr_le a a"
  sorry
end
