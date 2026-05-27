theory strncpy_Why3_ide_VCstrncpy_assign_normal_part13_goal18
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic"
begin
theorem goal18:
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_4 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int); x_1 :: int = (1 :: int) + i - i_1; a_3 :: addr \<Rightarrow> int = havoc t_1 t_3 a_2 x_1; x_2 :: int = i - i_1; a_4 :: addr = shift a x_2; a_5 :: addr = shift a_1 x_2; a_6 :: addr = shift a_1 x_1; x_3 :: int = to_uint32 (i - (1 :: int)) in \<not>i = (0 :: int) \<longrightarrow> a_3 a_4 = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_3 \<longrightarrow> is_sint8 i_4 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> p_length_of_str_is t t_3 a i_2 \<longrightarrow> p_length_of_str_is t t_3 a i_3 \<longrightarrow> valid_rw t a_2 i_1 \<longrightarrow> separated (shift a (0 :: int)) i_1 a_2 i_1 \<longrightarrow> addr_le a a_4 \<longrightarrow> addr_le a_1 a_5 \<longrightarrow> addr_le a_4 (shift a i_1) \<longrightarrow> addr_le a_5 (shift a_1 i_1) \<longrightarrow> valid_rw t a_6 x_3 \<longrightarrow> \<not>invalid t a_6 x_3 \<longrightarrow> (\<not>i_1 = i \<longrightarrow> \<not>i_4 = (0 :: int)) \<longrightarrow> (\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 < x_3 \<longrightarrow> havoc t_2 (a_3(a_5 := 0 :: int)) a_6 x_3 (shift a_1 ((1 :: int) + i_5 + i - i_1)) = (0 :: int)) \<longrightarrow> included a_6 x_3 a_2 i_1"
  sorry
end
