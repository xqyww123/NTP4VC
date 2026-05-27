theory StrictUpperBoundForce_Why3_ide_VCStrictUpperBoundForce_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_equal_range2_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_equal_range2_lib.Compound_Compound"
begin
theorem goal0:
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "addr \<Rightarrow> int"
  assumes fact0: "i_1 < i_2"
  assumes fact1: "i_3 \<le> i_1"
  assumes fact2: "region (base a) \<le> (0 :: int)"
  assumes fact3: "is_uint32 i_2"
  assumes fact4: "is_uint32 i_3"
  assumes fact5: "is_sint32 i"
  assumes fact6: "p_strictupperbound_1' t a i_3 i_2 i"
  shows "t (shift a i_1) < i"
  sorry
end
