theory strnlen_Why3_ide_VCstrnlen_smaller_post_part1_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal9:
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i - i_1; a_1 :: addr = shift a x in t_1 (shift a i_2) = (0 :: int) \<longrightarrow> t_1 a_1 = (0 :: int) \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rw t (shift a (0 :: int)) i \<longrightarrow> addr_le a a_1 \<longrightarrow> addr_le a_1 (shift a i) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 + i_1 < i \<longrightarrow> \<not>t_1 (shift a i_3) = (0 :: int)) \<longrightarrow> to_uint32 x \<le> i"
  sorry
end
