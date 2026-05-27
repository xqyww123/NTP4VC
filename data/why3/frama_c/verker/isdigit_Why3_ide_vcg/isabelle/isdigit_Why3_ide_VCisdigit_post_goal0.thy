theory isdigit_Why3_ide_VCisdigit_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Ctype_A_Ctype"
begin
theorem goal0:
  fixes i :: "int"
  fixes i_1 :: "int"
  assumes fact0: "is_sint32 i"
  assumes fact1: "is_sint32 i_1"
  assumes fact2: "if (48 :: int) \<le> i_1 then if i_1 \<le> (57 :: int) then i = (1 :: int) else i = (0 :: int) else i = (0 :: int)"
  shows "p_isdigit i_1 \<longleftrightarrow> \<not>i = (0 :: int)"
  sorry
end
