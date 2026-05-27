theory A_ToUpper_A_ToUpper
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Cint_Cint" "Axiomatic2_Axiomatic2"
begin
consts l_toupper :: "int \<Rightarrow> int"
axiomatization where Q_TL_ToUpper:   "is_sint8 (l_toupper c)"
 if "is_uint8 c"
  for c :: "int"
axiomatization where Q_to_upper_char'0:   "(32 :: int) + l_toupper c = c"
 if "is_uint8 c"
 and "p_is_lower c"
  for c :: "int"
axiomatization where Q_to_upper_char'1:   "\<forall>(i :: int). is_uint8 i \<longrightarrow> p_is_upper i \<longrightarrow> l_toupper i = i \<and> (\<forall>(i_1 :: int). is_uint8 i_1 \<longrightarrow> \<not>p_is_lower i_1 \<longrightarrow> \<not>p_is_upper i_1 \<longrightarrow> l_toupper i_1 = i_1)"
 if "is_uint8 c"
 and "p_is_lower c"
  for c :: "int"
end
