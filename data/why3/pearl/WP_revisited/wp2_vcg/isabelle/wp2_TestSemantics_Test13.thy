theory wp2_TestSemantics_Test13
  imports "NTP4Verif.NTP4Verif" "Why3STD.map_Const" "pearl_WP_revisited_lib.wp2_Imp"
begin
theorem Test13:
  shows "eval_term ((const :: value \<Rightarrow> int \<Rightarrow> value) (Vint (0 :: int))) ((const :: value \<Rightarrow> int \<Rightarrow> value) (Vint (42 :: int))) (Tconst (13 :: int)) = Vint (13 :: int)"
  sorry
end
