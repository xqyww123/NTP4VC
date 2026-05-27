theory memchr_Why3_ide_VCmemchr_not_found_post_part1_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal11:
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (i - i_1); x :: int = t_1 a_1 in \<not>i_1 = (0 :: int) \<longrightarrow> x = to_sint8 i_2 \<longrightarrow> (0 :: int) < i \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> -(128 :: int) \<le> i_2 \<longrightarrow> i_2 \<le> (127 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> valid_rw t (shift a (0 :: int)) i \<longrightarrow> addr_le a a_1 \<longrightarrow> addr_le a_1 (shift a i) \<longrightarrow> is_sint8 x \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i \<longrightarrow> \<not>x = t_1 (shift a i_3)) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 + i_1 < i \<longrightarrow> \<not>x = t_1 (shift a i_3)) \<longrightarrow> a_1 = Mk_addr (0 :: int) (0 :: int)"
  sorry
end
