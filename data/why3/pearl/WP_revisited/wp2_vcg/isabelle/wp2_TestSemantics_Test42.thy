theory wp2_TestSemantics_Test42
  imports "NTP4Verif.NTP4Verif" "Why3STD.map_Const" "pearl_WP_revisited_lib.wp2_Imp"
begin
theorem Test42:
  shows "eval_term ((const :: value \<Rightarrow> int \<Rightarrow> value) (Vint (0 :: int))) ((const :: value \<Rightarrow> int \<Rightarrow> value) (Vint (42 :: int))) (Tvar (0 :: int)) = Vint (42 :: int)"
  sorry
end
