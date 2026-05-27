theory wp2_HoareLogic_assert_rule_extqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_WP_revisited_lib.wp2_Imp"
begin
theorem assert_rule_ext'vc:
  fixes f :: "fmla"
  fixes p :: "fmla"
  shows "valid_triple (Fimplies f p) (Sassert f) p"
  sorry
end
