theory is_sorted_Why3_ide_VCis_sorted_assert_rte_unsigned_overflow_2_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_is_sorted_lib.Compound_Compound" "frama_c_standard_algorithms_is_sorted_lib.Axiomatic_Axiomatic"
begin
theorem goal5:
  fixes i :: "int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "(0 :: int) < i"
  assumes fact1: "region (base a) \<le> (0 :: int)"
  assumes fact2: "(2 :: int) + i_1 \<le> i"
  assumes fact3: "linked t"
  assumes fact4: "is_uint32 i"
  assumes fact5: "is_uint32 i_1"
  assumes fact6: "valid_rd t (shift a (0 :: int)) i"
  assumes fact7: "p_weaklysorted_1' t_1 a (0 :: int) ((1 :: int) + i_1)"
  shows "i_1 \<le> (4294967294 :: int)"
  sorry
end
