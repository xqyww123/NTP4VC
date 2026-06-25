theory hackers_delight_Utils_Spec_countSpec_Auxqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.int_NumOf" "./hackers_delight_Utils"
begin
consts nth_closure :: "32 word \<Rightarrow> int \<Rightarrow> bool"
axiomatization where nth_closure_def:   "nth_closure y y1 = ((0 \<le> y1 \<and> bit y (nat y1)))"
  for y :: "32 word"
  and y1 :: "int"
theorem countSpec_Aux'vc:
  fixes bv :: "32 word"
  shows "uint (hackers_delight_Utils.count bv) = numof (nth_closure bv) (0 :: int) (32 :: int)"
  sorry
end
