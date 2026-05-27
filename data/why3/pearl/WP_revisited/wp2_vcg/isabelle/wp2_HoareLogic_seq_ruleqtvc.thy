theory wp2_HoareLogic_seq_ruleqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_WP_revisited_lib.wp2_Imp"
begin
theorem seq_rule'vc:
  fixes p :: "fmla"
  fixes i1 :: "stmt"
  fixes r :: "fmla"
  fixes i2 :: "stmt"
  fixes q :: "fmla"
  assumes fact0: "valid_triple p i1 r"
  assumes fact1: "valid_triple r i2 q"
  shows "valid_triple p (Sseq i1 i2) q"
  sorry
end
