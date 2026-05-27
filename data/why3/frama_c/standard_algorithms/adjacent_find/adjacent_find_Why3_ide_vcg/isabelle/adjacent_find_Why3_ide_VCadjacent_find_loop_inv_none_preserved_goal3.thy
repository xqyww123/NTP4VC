theory adjacent_find_Why3_ide_VCadjacent_find_loop_inv_none_preserved_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_adjacent_find_lib.Compound_Compound" "frama_c_standard_algorithms_adjacent_find_lib.Axiomatic_Axiomatic"
begin
theorem goal3:
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = (1 :: int) + i_1; a_1 :: addr = shift a x; x_1 :: int = t_1 a_1; a_2 :: addr = shift a i_1; x_2 :: int = t_1 a_2; x_3 :: int = (2 :: int) + i_1 in \<not>x_1 = x_2 \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> i_1 \<le> (4294967294 :: int) \<longrightarrow> x_3 \<le> i \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 x \<longrightarrow> is_sint32 x_2 \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> \<not>p_hasequalneighbors t_1 a x \<longrightarrow> is_sint32 x_1 \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> \<not>p_hasequalneighbors t_1 a x_3"
  sorry
end
