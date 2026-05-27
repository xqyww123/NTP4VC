theory partial_sort_Why3_ide_VCpartial_sort_post_sorted_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_partial_sort_lib.Compound_Compound" "frama_c_standard_algorithms_partial_sort_lib.Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "i_1 \<le> (0 :: int)"
  assumes fact1: "i_1 \<le> i"
  assumes fact2: "(0 :: int) \<le> i_1"
  assumes fact3: "region (base a) \<le> (0 :: int)"
  assumes fact4: "linked t"
  assumes fact5: "is_uint32 i"
  assumes fact6: "is_uint32 i_1"
  assumes fact7: "valid_rw t (shift a (0 :: int)) i"
  shows "p_sorted_1' t_1 a (0 :: int) (0 :: int)"
  sorry
end
