theory wp2_TestSemantics_Test55
  imports "NTP4Verif.NTP4Verif" "Why3STD.map_Const" "pearl_WP_revisited_lib.wp2_Imp"
begin
theorem Test55:
  shows "eval_term ((const :: value \<Rightarrow> int \<Rightarrow> value) (Vint (0 :: int))) ((const :: value \<Rightarrow> int \<Rightarrow> value) (Vint (42 :: int))) (Tbin (Tvar (0 :: int)) Oplus (Tconst (13 :: int))) = Vint (55 :: int)"
  sorry
end
