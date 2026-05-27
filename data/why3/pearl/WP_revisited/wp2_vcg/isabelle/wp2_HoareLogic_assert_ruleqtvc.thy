theory wp2_HoareLogic_assert_ruleqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_WP_revisited_lib.wp2_Imp"
begin
theorem assert_rule'vc:
  fixes p :: "fmla"
  fixes f :: "fmla"
  assumes fact0: "valid_fmla (Fimplies p f)"
  shows "valid_triple p (Sassert f) p"
  sorry
end
