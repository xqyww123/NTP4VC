theory wp2_HoareLogic_consequence_ruleqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_WP_revisited_lib.wp2_Imp"
begin
theorem consequence_rule'vc:
  fixes p' :: "fmla"
  fixes p :: "fmla"
  fixes i :: "stmt"
  fixes q :: "fmla"
  fixes q' :: "fmla"
  assumes fact0: "valid_fmla (Fimplies p' p)"
  assumes fact1: "valid_triple p i q"
  assumes fact2: "valid_fmla (Fimplies q q')"
  shows "valid_triple p' i q'"
  sorry
end
