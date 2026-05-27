theory toupper_Why3_ide_VCtoupper_else_post_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic2_Axiomatic2"
begin
theorem goal4:
  fixes i_1 :: "int"
  fixes i :: "int"
  shows "let x :: int = to_uint8 i_1 in (0 :: int) \<le> i_1 \<longrightarrow> i_1 \<le> (255 :: int) \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> \<not>p_is_lower x \<longrightarrow> \<not>p_is_upper x \<longrightarrow> i_1 = i"
  sorry
end
