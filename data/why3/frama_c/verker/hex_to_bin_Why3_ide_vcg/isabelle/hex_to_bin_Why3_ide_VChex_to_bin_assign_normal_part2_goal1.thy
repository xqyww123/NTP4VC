theory hex_to_bin_Why3_ide_VChex_to_bin_assign_normal_part2_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Ctype_A_Ctype"
begin
theorem goal1:
  fixes i :: "int"
  assumes fact0: "is_sint8 i"
  assumes fact1: "is_sint8 (l_tolower i)"
  shows "\<not>(i \<le> (47 :: int) \<or> (58 :: int) \<le> i)"
  sorry
end
