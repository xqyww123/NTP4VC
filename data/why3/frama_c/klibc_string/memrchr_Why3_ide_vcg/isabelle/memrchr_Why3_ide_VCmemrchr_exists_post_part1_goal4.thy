theory memrchr_Why3_ide_VCmemrchr_exists_post_part1_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal4:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 (shift a (i - (1 :: int))); x_1 :: int = t_1 (shift a i_2) in \<not>i = (0 :: int) \<longrightarrow> x = to_sint8 x_1 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> -(128 :: int) \<le> x_1 \<longrightarrow> x_1 \<le> (126 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint32 x_1 \<longrightarrow> valid_rw t (shift a (0 :: int)) i_1 \<longrightarrow> is_sint8 x \<longrightarrow> (\<forall>(i_3 :: int). i \<le> i_3 \<longrightarrow> i_3 < i_1 \<longrightarrow> \<not>x_1 = t_1 (shift a i_3)) \<longrightarrow> (\<exists>(i_3 :: int). let x_2 :: int = t_1 (shift a i_3) in (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_1 \<longrightarrow> (1 :: int) + i_3 = i \<and> x_1 = x_2 \<and> (\<forall>(i_4 :: int). i_4 < i_1 \<longrightarrow> i_3 < i_4 \<longrightarrow> \<not>x_1 = x_2))"
  sorry
end
