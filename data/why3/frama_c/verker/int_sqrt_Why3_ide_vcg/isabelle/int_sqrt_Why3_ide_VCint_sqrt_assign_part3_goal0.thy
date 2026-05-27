theory int_sqrt_Why3_ide_VCint_sqrt_assign_part3_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes i :: "int"
  assumes fact0: "(2 :: int) \<le> i"
  shows "\<not>is_uint64 i"
  sorry
end
