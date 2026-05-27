theory wp2_HoareLogic_while_ruleqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_WP_revisited_lib.wp2_Imp"
begin
theorem while_rule'vc:
  fixes e :: "term"
  fixes inv :: "fmla"
  fixes i :: "stmt"
  assumes fact0: "valid_triple (Fand (Fterm e) inv) i inv"
  shows "valid_triple inv (Swhile e inv i) (Fand (Fnot (Fterm e)) inv)"
  sorry
end
