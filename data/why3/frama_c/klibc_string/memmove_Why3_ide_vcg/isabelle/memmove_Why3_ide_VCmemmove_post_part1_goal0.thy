theory memmove_Why3_ide_VCmemmove_post_part1_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal0:
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 i; a_3 :: addr = shift a i; a_4 :: addr = shift a_1 (0 :: int); a_5 :: addr \<Rightarrow> int = havoc t_1 t_2 a_4 i in (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i \<longrightarrow> addr_lt a_1 a \<longrightarrow> addr_lt a_2 a_3 \<longrightarrow> addr_le a a_3 \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> addr_le a_3 a_3 \<longrightarrow> addr_le a_2 a_2 \<longrightarrow> valid_rw t (shift a (0 :: int)) i \<longrightarrow> valid_rw t a_4 i \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> a_5 (shift a_1 i_2) = t_2 (shift a i_2)) \<longrightarrow> a_5 (shift a_1 i_1) = t_2 (shift a i_1)"
  sorry
end
