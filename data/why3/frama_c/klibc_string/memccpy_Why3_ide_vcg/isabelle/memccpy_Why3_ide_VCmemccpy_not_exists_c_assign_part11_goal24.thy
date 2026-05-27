theory memccpy_Why3_ide_VCmemccpy_not_exists_c_assign_part11_goal24
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal24:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a_1 (0 :: int); x :: int = i_1 - i; a_4 :: addr = shift a x; a_5 :: addr = shift a_1 x; x_1 :: int = to_sint8 i_2; a_6 :: addr \<Rightarrow> int = havoc t_1 t_2 a_3 x in \<not>i = (0 :: int) \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> -(128 :: int) \<le> i_2 \<longrightarrow> i_2 \<le> (127 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> valid_rw t a_2 i_1 \<longrightarrow> valid_rw t a_3 i_1 \<longrightarrow> separated a_2 i_1 a_3 i_1 \<longrightarrow> addr_le a a_4 \<longrightarrow> addr_le a_1 a_5 \<longrightarrow> addr_le a_4 (shift a i_1) \<longrightarrow> addr_le a_5 (shift a_1 i_1) \<longrightarrow> \<not>invalid t a_5 (1 :: int) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_1 \<longrightarrow> \<not>t_2 (shift a i_3) = x_1) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 + i < i_1 \<longrightarrow> a_6 (shift a_1 i_3) = a_6 (shift a i_3)) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 + i < i_1 \<longrightarrow> \<not>a_6 (shift a_1 i_3) = x_1) \<longrightarrow> included a_5 (1 :: int) a_3 i_1"
  sorry
end
