theory is_sorted_Why3_ide_VCis_sorted_loop_inv_sorted_preserved_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_is_sorted_lib.Compound_Compound" "frama_c_standard_algorithms_is_sorted_lib.Axiomatic_Axiomatic"
begin
theorem goal1:
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a i_1; x :: int = t_1 a_1; x_1 :: int = (1 :: int) + i_1; a_2 :: addr = shift a x_1; x_2 :: int = t_1 a_2; x_3 :: int = (2 :: int) + i_1 in (0 :: int) < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> x \<le> x_2 \<longrightarrow> i_1 \<le> (4294967294 :: int) \<longrightarrow> x_3 \<le> i \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 x_1 \<longrightarrow> is_sint32 x \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> p_weaklysorted_1' t_1 a (0 :: int) x_1 \<longrightarrow> is_sint32 x_2 \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> p_weaklysorted_1' t_1 a (0 :: int) x_3"
  sorry
end
