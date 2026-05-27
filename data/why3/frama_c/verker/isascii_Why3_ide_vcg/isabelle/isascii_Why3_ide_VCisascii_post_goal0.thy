theory isascii_Why3_ide_VCisascii_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes i :: "int"
  assumes fact0: "is_sint8 i"
  shows "(0 :: int) \<le> i \<and> i \<le> (127 :: int) \<longleftrightarrow> to_uint8 i \<le> (127 :: int)"
  sorry
end
