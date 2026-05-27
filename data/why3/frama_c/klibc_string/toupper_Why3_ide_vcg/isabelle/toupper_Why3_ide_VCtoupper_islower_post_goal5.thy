theory toupper_Why3_ide_VCtoupper_islower_post_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic2_Axiomatic2"
begin
theorem goal5:
  fixes i_1 :: "int"
  fixes i :: "int"
  assumes fact0: "(0 :: int) \<le> i_1"
  assumes fact1: "i_1 \<le> (255 :: int)"
  assumes fact2: "is_sint32 i"
  assumes fact3: "is_sint32 i_1"
  assumes fact4: "p_is_lower (to_uint8 i_1)"
  shows "(32 :: int) + i = i_1"
  sorry
end
