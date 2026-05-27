theory wp2_HoareLogic_if_ruleqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_WP_revisited_lib.wp2_Imp"
begin
theorem if_rule'vc:
  fixes p :: "fmla"
  fixes e :: "term"
  fixes i1 :: "stmt"
  fixes q :: "fmla"
  fixes i2 :: "stmt"
  assumes fact0: "valid_triple (Fand p (Fterm e)) i1 q"
  assumes fact1: "valid_triple (Fand p (Fnot (Fterm e))) i2 q"
  shows "valid_triple p (Sif e i1 i2) q"
  sorry
end
