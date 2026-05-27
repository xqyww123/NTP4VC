theory memmove_Why3_ide_VCmemmove_loop_inv_18_preserved_goal27
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal27:
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i_1 - (1 :: int); a_2 :: addr = shift a i_1; a_3 :: addr = shift a_1 i_1; a_4 :: addr \<Rightarrow> int = havoc t_1 t_2 a_3 (i - i_1) in \<not>i_1 = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_2 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> to_uint32 x \<le> i_2 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> \<not>addr_lt a_1 a \<longrightarrow> addr_le a a_2 \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> addr_le a_2 (shift a i) \<longrightarrow> addr_le a_3 (shift a_1 i) \<longrightarrow> valid_rw t (shift a (0 :: int)) i \<longrightarrow> valid_rw t (shift a_1 (0 :: int)) i \<longrightarrow> (\<forall>(i_3 :: int). i_3 < i \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> a_4 (shift a_1 i_3) = t_2 (shift a i_3)) \<longrightarrow> (\<forall>(i_3 :: int). let a_5 :: addr = shift a_1 i_3 in (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_1 \<longrightarrow> a_4 a_5 = t_2 a_5) \<longrightarrow> (a_4(shift a_1 x := a_4 (shift a x))) (shift a_1 i_2) = t_2 (shift a i_2)"
  sorry
end
