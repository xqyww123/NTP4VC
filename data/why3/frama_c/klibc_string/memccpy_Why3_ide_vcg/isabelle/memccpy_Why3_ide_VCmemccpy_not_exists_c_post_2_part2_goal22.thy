theory memccpy_Why3_ide_VCmemccpy_not_exists_c_post_2_part2_goal22
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal22:
  fixes a :: "addr"
  fixes i :: "int"
  fixes a_1 :: "addr"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a i; a_3 :: addr = shift a_1 i; a_4 :: addr = shift a (0 :: int); a_5 :: addr = shift a_1 (0 :: int); x :: int = to_sint8 i_2; a_6 :: addr \<Rightarrow> int = havoc t_1 t_2 a_5 i in (0 :: int) < i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> -(128 :: int) \<le> i_2 \<longrightarrow> i_2 \<le> (127 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i \<longrightarrow> is_sint32 i_2 \<longrightarrow> addr_le a a_2 \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> addr_le a_2 a_2 \<longrightarrow> addr_le a_3 a_3 \<longrightarrow> valid_rw t a_4 i \<longrightarrow> valid_rw t a_5 i \<longrightarrow> separated a_4 i a_5 i \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i \<longrightarrow> \<not>t_2 (shift a i_3) = x) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i \<longrightarrow> a_6 (shift a_1 i_3) = a_6 (shift a i_3)) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i \<longrightarrow> \<not>a_6 (shift a_1 i_3) = x) \<longrightarrow> a_6 (shift a_1 i_1) = a_6 (shift a i_1)"
  sorry
end
