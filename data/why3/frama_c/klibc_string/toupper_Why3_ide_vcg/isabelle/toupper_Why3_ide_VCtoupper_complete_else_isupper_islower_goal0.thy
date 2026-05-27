theory toupper_Why3_ide_VCtoupper_complete_else_isupper_islower_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic2_Axiomatic2"
begin
theorem goal0:
  fixes i :: "int"
  shows "let x :: int = to_uint8 i in (0 :: int) \<le> i \<longrightarrow> i \<le> (255 :: int) \<longrightarrow> is_sint32 i \<longrightarrow> p_is_lower x \<or> p_is_upper x \<or> \<not>p_is_lower x \<and> \<not>p_is_upper x"
  sorry
end
