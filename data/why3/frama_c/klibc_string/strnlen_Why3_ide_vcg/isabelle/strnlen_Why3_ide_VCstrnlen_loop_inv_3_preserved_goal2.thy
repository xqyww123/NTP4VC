theory strnlen_Why3_ide_VCstrnlen_loop_inv_3_preserved_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal2:
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (i_1 - i); x :: int = t_1 a_1 in \<not>x = (0 :: int) \<longrightarrow> (0 :: int) < i \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rw t (shift a (0 :: int)) i_1 \<longrightarrow> addr_le a a_1 \<longrightarrow> addr_le a_1 (shift a i_1) \<longrightarrow> is_sint8 x \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 + i < i_1 \<longrightarrow> \<not>t_1 (shift a i_2) = (0 :: int)) \<longrightarrow> (1 :: int) + to_uint32 (i - (1 :: int)) = i"
  sorry
end
