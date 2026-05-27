theory memrchr_Why3_ide_VCmemrchr_exists_post_part2_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal5:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 (shift a i_1) in (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> -(128 :: int) \<le> x \<longrightarrow> x \<le> (126 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> is_sint8 (t_1 (shift a (-(1 :: int)))) \<longrightarrow> is_sint32 x \<longrightarrow> valid_rw t (shift a (0 :: int)) i \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> \<not>x = t_1 (shift a i_2)) \<longrightarrow> (\<exists>(i_2 :: int). let x_1 :: int = t_1 (shift a i_2) in (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> shift a i_2 = Mk_addr (0 :: int) (0 :: int) \<and> x = x_1 \<and> (\<forall>(i_3 :: int). i_3 < i \<longrightarrow> i_2 < i_3 \<longrightarrow> \<not>x = x_1))"
  sorry
end
