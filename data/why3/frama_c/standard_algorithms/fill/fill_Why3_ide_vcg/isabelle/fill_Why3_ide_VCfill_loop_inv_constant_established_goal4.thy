theory fill_Why3_ide_VCfill_loop_inv_constant_established_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_fill_lib.Compound_Compound" "frama_c_standard_algorithms_fill_lib.Axiomatic_Axiomatic"
begin
theorem goal4:
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "is_uint32 i_1"
  assumes fact3: "is_sint32 i"
  assumes fact4: "valid_rw t (shift a (0 :: int)) i_1"
  shows "p_constantrange t_1 a (0 :: int) (0 :: int) i"
  sorry
end
