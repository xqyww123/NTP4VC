theory hex_to_bin_Why3_ide_VChex_to_bin_to_digit_post_2_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Ctype_A_Ctype" "frama_c_verker_lib.A_HexToBin_A_HexToBin"
begin
theorem goal4:
  fixes i_3 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  shows "let x :: int = l_tolower i_3; x_1 :: int = (87 :: int) + i; x_2 :: int = (87 :: int) + i_1 in is_sint8 i_2 \<longrightarrow> is_sint8 i_3 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> p_isxdigit i_3 \<longrightarrow> (if (48 :: int) \<le> i_3 then if i_3 \<le> (57 :: int) then i_1 = i \<and> (48 :: int) + i_1 = i_3 else x = i_2 \<and> (if (97 :: int) \<le> i_2 then if i_2 \<le> (102 :: int) then x_1 = i_2 \<and> x_2 = i_2 else i = -(1 :: int) \<and> i_1 = -(1 :: int) else i = -(1 :: int) \<and> i_1 = -(1 :: int)) else x = i_2 \<and> (if (97 :: int) \<le> i_2 then if i_2 \<le> (102 :: int) then x_1 = i_2 \<and> x_2 = i_2 else i = -(1 :: int) \<and> i_1 = -(1 :: int) else i = -(1 :: int) \<and> i_1 = -(1 :: int))) \<longrightarrow> l_hex_to_bin i_3 = i_1"
  sorry
end
