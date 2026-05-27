theory toupper_Why3_ide_VCtoupper_isupper_post_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic2_Axiomatic2"
begin
theorem goal6:
  fixes i_1 :: "int"
  fixes i :: "int"
  assumes fact0: "(0 :: int) \<le> i_1"
  assumes fact1: "i_1 \<le> (255 :: int)"
  assumes fact2: "is_sint32 i"
  assumes fact3: "is_sint32 i_1"
  assumes fact4: "p_is_upper (to_uint8 i_1)"
  shows "i_1 = i"
  sorry
end
