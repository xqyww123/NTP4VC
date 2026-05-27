theory index_of_bounds_weak_Why3_ide_VCindex_of_bounds_weak_call_index_of_pre_part2_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list"
begin
theorem goal0:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  assumes fact0: "i_1 \<le> i"
  assumes fact1: "(0 :: int) \<le> i_1"
  assumes fact2: "region (base a) \<le> (0 :: int)"
  assumes fact3: "region (base a_1) \<le> (0 :: int)"
  assumes fact4: "framed t_1"
  assumes fact5: "linked t"
  assumes fact6: "is_sint32 i"
  assumes fact7: "is_sint32 i_1"
  assumes fact8: "valid_rw t (shift a_1 i_1) (i - i_1)"
  shows "(0 :: int) \<le> i"
  sorry
end
