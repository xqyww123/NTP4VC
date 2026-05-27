theory hex_to_bin_Why3_ide_VChex_to_bin_assign_exit_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes i :: "int"
  fixes i_1 :: "int"
  assumes fact0: "is_sint8 i"
  assumes fact1: "is_sint8 i_1"
  shows "\<not>(i \<le> (47 :: int) \<or> i_1 = i \<and> (58 :: int) \<le> i_1)"
  sorry
end
