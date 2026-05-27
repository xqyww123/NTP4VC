theory adjacent_find_Why3_ide_VCadjacent_find_post_result_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_adjacent_find_lib.Compound_Compound" "frama_c_standard_algorithms_adjacent_find_lib.Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes p :: "bool"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let x :: int = (1 :: int) + i_1; x_1 :: int = (1 :: int) + i_2; a_1 :: addr = shift a i_2 in region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> (if (2 :: int) \<le> i then p = False \<and> (0 :: int) \<le> i_1 \<and> i_1 < i \<and> i_1 \<le> (4294967294 :: int) \<and> \<not>p_hasequalneighbors t_1 a x \<and> (if (2 :: int) + i_1 \<le> i then i_2 = i_1 \<and> t_1 (shift a x_1) = t_1 a_1 \<and> valid_rd t a_1 (1 :: int) \<and> valid_rd t (shift a (to_uint32 x_1)) (1 :: int) else x = i_2) else i_2 = i) \<longrightarrow> i_2 \<le> i \<and> (0 :: int) \<le> i_2"
  sorry
end
