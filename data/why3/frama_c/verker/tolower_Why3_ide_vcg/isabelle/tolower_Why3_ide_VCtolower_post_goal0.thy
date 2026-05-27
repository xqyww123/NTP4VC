theory tolower_Why3_ide_VCtolower_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Ctype_A_Ctype"
begin
theorem goal0:
  fixes i :: "int"
  shows "let x :: int = l_tolower (to_uint8 i) in is_sint8 i \<longrightarrow> is_uint8 x \<longrightarrow> to_sint8 x = l_tolower i"
  sorry
end
