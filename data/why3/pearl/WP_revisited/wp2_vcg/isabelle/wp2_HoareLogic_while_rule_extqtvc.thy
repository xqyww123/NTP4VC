theory wp2_HoareLogic_while_rule_extqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_WP_revisited_lib.wp2_Imp"
begin
theorem while_rule_ext'vc:
  fixes inv' :: "fmla"
  fixes inv :: "fmla"
  fixes e :: "term"
  fixes i :: "stmt"
  assumes fact0: "valid_fmla (Fimplies inv' inv)"
  assumes fact1: "valid_triple (Fand (Fterm e) inv') i inv'"
  shows "valid_triple inv' (Swhile e inv i) (Fand (Fnot (Fterm e)) inv')"
  sorry
end
