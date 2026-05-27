theory wp2_TestSemantics_Test0
  imports "NTP4Verif.NTP4Verif" "Why3STD.map_Const" "pearl_WP_revisited_lib.wp2_Imp"
begin
theorem Test0:
  shows "eval_term ((const :: value \<Rightarrow> int \<Rightarrow> value) (Vint (0 :: int))) ((const :: value \<Rightarrow> int \<Rightarrow> value) (Vint (42 :: int))) (Tderef (0 :: int)) = Vint (0 :: int)"
  sorry
end
