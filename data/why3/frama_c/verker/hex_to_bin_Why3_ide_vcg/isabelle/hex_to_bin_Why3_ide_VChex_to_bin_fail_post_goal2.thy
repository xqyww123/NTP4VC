theory hex_to_bin_Why3_ide_VChex_to_bin_fail_post_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Ctype_A_Ctype"
begin
theorem goal2:
  fixes i_4 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i_5 :: "int"
  shows "let x :: int = l_tolower i_4; x_1 :: int = (87 :: int) + i; x_2 :: int = (87 :: int) + i_1 in is_sint8 i_2 \<longrightarrow> is_sint8 i_3 \<longrightarrow> is_sint8 i_4 \<longrightarrow> is_sint8 i_5 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> \<not>p_isxdigit i_2 \<longrightarrow> (if (48 :: int) \<le> i_2 then i_3 = i_2 \<and> (if i_3 \<le> (57 :: int) then i_1 = i \<and> (48 :: int) + i_1 = i_3 else i_4 = i_3 \<and> x = i_5 \<and> (if (97 :: int) \<le> i_5 then if i_5 \<le> (102 :: int) then x_1 = i_5 \<and> x_2 = i_5 else i = -(1 :: int) \<and> i_1 = -(1 :: int) else i = -(1 :: int) \<and> i_1 = -(1 :: int))) else i_4 = i_2 \<and> x = i_5 \<and> (if (97 :: int) \<le> i_5 then if i_5 \<le> (102 :: int) then x_1 = i_5 \<and> x_2 = i_5 else i = -(1 :: int) \<and> i_1 = -(1 :: int) else i = -(1 :: int) \<and> i_1 = -(1 :: int))) \<longrightarrow> i_1 = -(1 :: int)"
  sorry
end
