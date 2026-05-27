theory check_bytes8_Why3_ide_VCcheck_bytes8_loop_inv_4_established_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal7:
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "is_uint8 i"
  assumes fact3: "is_uint32 i_1"
  assumes fact4: "addr_lt a_1 a"
  assumes fact5: "addr_le a a_1"
  assumes fact6: "valid_rd t (shift a (0 :: int)) i_1"
  shows "t_1 a_1 = i"
  sorry
end
