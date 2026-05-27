theory accumulate_Why3_ide_VCaccumulate_loop_inv_index_established_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_accumulate_lib.A_AccumulateAxiomatic_A_AccumulateAxiomatic" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_accumulate_lib.Compound_Compound" "frama_c_standard_algorithms_accumulate_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_accumulate_lib.Axiomatic1_Axiomatic1"
begin
theorem goal1:
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "is_uint32 i"
  assumes fact3: "is_sint32 i_1"
  assumes fact4: "p_accumulatebounds_1' t_1 a i i_1"
  assumes fact5: "valid_rd t (shift a (0 :: int)) i"
  shows "(0 :: int) \<le> i"
  sorry
end
