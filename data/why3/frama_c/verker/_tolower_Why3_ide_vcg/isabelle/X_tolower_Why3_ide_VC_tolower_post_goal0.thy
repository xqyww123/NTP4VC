theory X_tolower_Why3_ide_VC_tolower_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Cint_Cint" "Why3STD.Cbits_Cbits" "frama_c_verker_lib.A_Ctype_A_Ctype"
begin
theorem goal0:
  fixes i :: "int"
  assumes fact0: "is_sint8 i"
  shows "to_sint8 (lor (32 :: int) i) = l_tolower i"
  sorry
end
