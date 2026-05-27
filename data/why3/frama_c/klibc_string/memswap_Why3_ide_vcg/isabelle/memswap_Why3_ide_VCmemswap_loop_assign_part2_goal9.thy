theory memswap_Why3_ide_VCmemswap_loop_assign_part2_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal9:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a_1 (0 :: int); x :: int = i_1 - i; a_4 :: addr \<Rightarrow> int = havoc t_2 (havoc t_1 t_3 a_2 x) a_3 x; x_1 :: int = to_uint32 (i - (1 :: int)) in \<not>i = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_3 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rw t a_2 i_1 \<longrightarrow> valid_rw t a_3 i_1 \<longrightarrow> \<not>invalid t a_3 x \<longrightarrow> separated a_3 i_1 a_2 i_1 \<longrightarrow> (\<forall>(i_2 :: int). let a_5 :: addr = shift a i_2 in i_2 < i_1 \<longrightarrow> i_1 \<le> i_2 + i \<longrightarrow> a_4 a_5 = t_3 a_5) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 + i < i_1 \<longrightarrow> a_4 (shift a i_2) = t_3 (shift a_1 i_2)) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 + i < i_1 \<longrightarrow> a_4 (shift a_1 i_2) = t_3 (shift a i_2)) \<longrightarrow> (\<forall>(i_2 :: int). let a_5 :: addr = shift a_1 i_2 in i_2 < i_1 \<longrightarrow> i_1 \<le> i_2 + i \<longrightarrow> a_4 a_5 = t_3 a_5) \<longrightarrow> included a_3 x a_2 (i_1 - x_1) \<or> (i < i_1 \<longrightarrow> x_1 \<le> i)"
  sorry
end
