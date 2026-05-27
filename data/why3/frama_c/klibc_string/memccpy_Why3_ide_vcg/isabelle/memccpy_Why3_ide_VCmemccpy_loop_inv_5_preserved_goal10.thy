theory memccpy_Why3_ide_VCmemccpy_loop_inv_5_preserved_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal10:
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int); x :: int = i_1 - i; a_3 :: addr \<Rightarrow> int = havoc t_1 t_2 a_2 x; a_4 :: addr = shift a x; a_5 :: int = a_3 a_4; x_1 :: int = to_sint8 i_2; a_6 :: addr = shift a (0 :: int); a_7 :: addr = shift a_1 x in \<not>i = (0 :: int) \<longrightarrow> \<not>a_5 = x_1 \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> -(128 :: int) \<le> i_2 \<longrightarrow> i_2 \<le> (127 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> valid_rw t a_6 i_1 \<longrightarrow> valid_rw t a_2 i_1 \<longrightarrow> separated a_6 i_1 a_2 i_1 \<longrightarrow> addr_le a a_4 \<longrightarrow> addr_le a_1 a_7 \<longrightarrow> addr_le a_4 (shift a i_1) \<longrightarrow> addr_le a_7 (shift a_1 i_1) \<longrightarrow> is_sint8 a_5 \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 + i < i_1 \<longrightarrow> a_3 (shift a_1 i_3) = a_3 (shift a i_3)) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 + i < i_1 \<longrightarrow> \<not>a_3 (shift a_1 i_3) = x_1) \<longrightarrow> (1 :: int) + to_uint32 (i - (1 :: int)) = i"
  sorry
end
