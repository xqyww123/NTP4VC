theory toupper_Why3_ide_VCtoupper_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Ctype_A_Ctype"
begin
theorem goal0:
  fixes i :: "int"
  shows "let x :: int = l_toupper (to_uint8 i) in is_sint8 i \<longrightarrow> is_uint8 x \<longrightarrow> to_sint8 x = l_toupper i"
  sorry
end
