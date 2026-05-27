theory CountSectionUnion_Why3_ide_VCCountSectionUnion_loop_inv_2_established_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_insertion_sort_lib.A_Count_A_Count" "frama_c_standard_algorithms_insertion_sort_lib.Compound_Compound" "frama_c_standard_algorithms_insertion_sort_lib.Axiomatic_Axiomatic"
begin
theorem goal3:
  fixes i_3 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes t :: "addr \<Rightarrow> int"
  assumes fact0: "i_3 \<le> i"
  assumes fact1: "i_1 \<le> i_3"
  assumes fact2: "region (base a) \<le> (0 :: int)"
  assumes fact3: "is_uint32 i"
  assumes fact4: "is_uint32 i_1"
  assumes fact5: "is_uint32 i_3"
  assumes fact6: "is_sint32 i_2"
  shows "l_count_1' t a i_3 i_3 i_2 = (0 :: int)"
  sorry
end
