theory memswap_Why3_ide_VCmemswap_loop_assign_part4_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal11:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a_1 (0 :: int); x :: int = i_1 - i; a_4 :: addr = shift a_1 x; a_5 :: addr \<Rightarrow> int = havoc t_2 (havoc t_1 t_3 a_2 x) a_3 x; x_1 :: int = i_1 - to_uint32 (i - (1 :: int)) in \<not>i = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_3 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rw t a_2 i_1 \<longrightarrow> valid_rw t a_3 i_1 \<longrightarrow> separated a_3 i_1 a_2 i_1 \<longrightarrow> \<not>invalid t a_4 (1 :: int) \<longrightarrow> (\<forall>(i_2 :: int). let a_6 :: addr = shift a i_2 in i_2 < i_1 \<longrightarrow> i_1 \<le> i_2 + i \<longrightarrow> a_5 a_6 = t_3 a_6) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 + i < i_1 \<longrightarrow> a_5 (shift a i_2) = t_3 (shift a_1 i_2)) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 + i < i_1 \<longrightarrow> a_5 (shift a_1 i_2) = t_3 (shift a i_2)) \<longrightarrow> (\<forall>(i_2 :: int). let a_6 :: addr = shift a_1 i_2 in i_2 < i_1 \<longrightarrow> i_1 \<le> i_2 + i \<longrightarrow> a_5 a_6 = t_3 a_6) \<longrightarrow> included a_4 (1 :: int) a_2 x_1 \<or> included a_4 (1 :: int) a_3 x_1"
  sorry
end
