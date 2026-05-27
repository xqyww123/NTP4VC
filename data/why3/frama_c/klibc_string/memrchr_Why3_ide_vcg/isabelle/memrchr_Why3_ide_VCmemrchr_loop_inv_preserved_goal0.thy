theory memrchr_Why3_ide_VCmemrchr_loop_inv_preserved_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i - (1 :: int); x_1 :: int = t_1 (shift a x) in \<not>i = (0 :: int) \<longrightarrow> \<not>x_1 = to_sint8 i_2 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> -(128 :: int) \<le> i_2 \<longrightarrow> i_2 \<le> (126 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> valid_rw t (shift a (0 :: int)) i_1 \<longrightarrow> is_sint8 x_1 \<longrightarrow> (\<forall>(i_3 :: int). i \<le> i_3 \<longrightarrow> i_3 < i_1 \<longrightarrow> \<not>t_1 (shift a i_3) = i_2) \<longrightarrow> (1 :: int) + to_uint32 x = i"
  sorry
end
