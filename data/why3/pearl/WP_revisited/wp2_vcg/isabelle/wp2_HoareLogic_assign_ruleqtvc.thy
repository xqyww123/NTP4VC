theory wp2_HoareLogic_assign_ruleqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_WP_revisited_lib.wp2_Imp"
begin
theorem assign_rule'vc:
  fixes id1 :: "int"
  fixes q :: "fmla"
  fixes e :: "term"
  fixes x :: "int"
  assumes fact0: "fresh_in_fmla id1 q"
  shows "valid_triple (Flet id1 e (subst q x id1)) (Sassign x e) q"
  sorry
end
