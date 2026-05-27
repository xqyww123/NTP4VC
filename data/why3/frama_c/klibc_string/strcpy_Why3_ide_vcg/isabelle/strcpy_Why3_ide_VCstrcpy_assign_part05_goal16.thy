theory strcpy_Why3_ide_VCstrcpy_assign_part05_goal16
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "Why3STD.Cint_Cint"
begin
theorem goal16:
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int); x :: int = (1 :: int) + l_length t_1 a in \<not>a_1 = a \<longrightarrow> (0 :: int) < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_1 \<le> (2000 :: int) \<longrightarrow> i_2 \<le> (2000 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> p_length_of_str_is t t_1 a i_1 \<longrightarrow> p_length_of_str_is t t_1 a i_2 \<longrightarrow> \<not>invalid t a_2 i \<longrightarrow> valid_rw t a_2 x \<longrightarrow> separated (shift a (0 :: int)) x a_2 x \<longrightarrow> i \<le> x"
  sorry
end
