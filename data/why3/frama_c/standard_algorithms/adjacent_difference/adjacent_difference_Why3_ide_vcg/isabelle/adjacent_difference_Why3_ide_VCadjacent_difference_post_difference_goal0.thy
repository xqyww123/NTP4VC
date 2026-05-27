theory adjacent_difference_Why3_ide_VCadjacent_difference_post_difference_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_adjacent_difference_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_adjacent_difference_lib.Compound_Compound" "frama_c_standard_algorithms_adjacent_difference_lib.A_DifferenceAxiomatic_A_DifferenceAxiomatic" "frama_c_standard_algorithms_adjacent_difference_lib.Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes p :: "bool"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int); a_3 :: addr = shift a (0 :: int) in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> p_adjacentdifferencebounds t_3 a_1 i \<longrightarrow> valid_rd t a_2 i \<longrightarrow> valid_rw t a_3 i \<longrightarrow> separated a_2 i a_3 i \<longrightarrow> (if (0 :: int) < i then p = False \<and> havoc t_1 (t_3(a_3 := t_3 a_2)) (shift a (1 :: int)) (i - (1 :: int)) = t_2 \<and> (0 :: int) < i_1 \<and> i_1 \<le> i \<and> i \<le> i_1 \<and> p_unchanged_1' t_2 t_3 a_1 (0 :: int) i \<and> p_adjacentdifference t_2 a_1 i_1 a \<and> valid_rd t a_2 (1 :: int) \<and> valid_rw t a_3 (1 :: int) else t_3 = t_2) \<longrightarrow> p_adjacentdifference t_2 a_1 i a"
  sorry
end
