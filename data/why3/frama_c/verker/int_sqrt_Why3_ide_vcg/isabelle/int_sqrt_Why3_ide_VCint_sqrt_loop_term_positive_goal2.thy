theory int_sqrt_Why3_ide_VCint_sqrt_loop_term_positive_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Cint_Cint"
begin
theorem goal2:
  fixes i_1 :: "int"
  fixes i :: "int"
  assumes fact0: "\<not>i_1 = (0 :: int)"
  assumes fact1: "(2 :: int) \<le> i"
  assumes fact2: "is_uint64 i"
  assumes fact3: "is_uint64 i_1"
  shows "(0 :: int) \<le> i_1"
  sorry
end
