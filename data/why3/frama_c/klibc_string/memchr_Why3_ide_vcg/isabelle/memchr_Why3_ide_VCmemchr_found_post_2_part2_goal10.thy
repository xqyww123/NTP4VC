theory memchr_Why3_ide_VCmemchr_found_post_2_part2_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal10:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 (shift a i_1); x_1 :: int = t_1 (Mk_addr (0 :: int) (0 :: int)); a_1 :: addr = shift a i in x = to_sint8 i_2 \<longrightarrow> (0 :: int) < i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> -(128 :: int) \<le> i_2 \<longrightarrow> i_2 \<le> (127 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_sint8 x_1 \<longrightarrow> addr_le a a_1 \<longrightarrow> addr_le a_1 a_1 \<longrightarrow> is_sint8 (t_1 a_1) \<longrightarrow> valid_rw t (shift a (0 :: int)) i \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i \<longrightarrow> \<not>x = t_1 (shift a i_3)) \<longrightarrow> x = x_1"
  sorry
end
