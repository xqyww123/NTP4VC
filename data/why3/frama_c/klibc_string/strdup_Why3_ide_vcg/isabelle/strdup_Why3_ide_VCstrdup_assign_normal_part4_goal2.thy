theory strdup_Why3_ide_VCstrdup_assign_normal_part4_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal2:
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  shows "let x :: int = l_length t_2 a; x_1 :: int = (1 :: int) + x; x_2 :: int = to_uint32 x_1; a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a_1 (0 :: int); a_4 :: addr \<Rightarrow> int = havoc t_1 t_2 a_3 x_2 in \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x_2 = (0 :: int) \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint32 x \<longrightarrow> p_length_of_str_is t t_2 a i \<longrightarrow> p_length_of_str_is t t_2 a i_1 \<longrightarrow> p_length_of_str_is t t_2 a i_2 \<longrightarrow> is_sint32 x_1 \<longrightarrow> valid_rw t a_2 x_2 \<longrightarrow> valid_rw t a_3 x_2 \<longrightarrow> separated a_2 x_2 a_3 x_2 \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < x_2 \<longrightarrow> a_4 (shift a_1 i_3) = a_4 (shift a i_3)) \<longrightarrow> invalid t a_3 x_2"
  sorry
end
