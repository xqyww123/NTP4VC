theory adjacent_find_Why3_ide_VCadjacent_find_some_post_adjacent_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_adjacent_find_lib.Compound_Compound" "frama_c_standard_algorithms_adjacent_find_lib.Axiomatic_Axiomatic"
begin
theorem goal10:
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  shows "let a_1 :: addr = shift a i_2; x :: int = t_1 a_1; x_1 :: int = (1 :: int) + i_2; x_2 :: int = t_1 (shift a x_1); x_3 :: int = (1 :: int) + i_1 in region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> p_hasequalneighbors t_1 a i \<longrightarrow> is_sint32 x \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> is_sint32 x_2 \<longrightarrow> (if (2 :: int) \<le> i then (0 :: int) \<le> i_1 \<and> i_1 < i \<and> i_1 \<le> (4294967294 :: int) \<and> \<not>p_hasequalneighbors t_1 a x_3 \<and> (if (2 :: int) + i_1 \<le> i then i_2 = i_1 \<and> x_2 = x \<and> valid_rd t a_1 (1 :: int) \<and> valid_rd t (shift a (to_uint32 x_1)) (1 :: int) else x_3 = i_2) else i_2 = i) \<longrightarrow> x_2 = x"
  sorry
end
