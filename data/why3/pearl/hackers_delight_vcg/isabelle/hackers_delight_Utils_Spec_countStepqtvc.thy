theory hackers_delight_Utils_Spec_countStepqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.int_NumOf" "./hackers_delight_Utils"
begin
theorem countStep'vc:
  fixes b :: "32 word"
  shows "\<not>(bit b (unat (0 :: 32 word))) = True \<longleftrightarrow> hackers_delight_Utils.count (b >> unat (1 :: 32 word)) = hackers_delight_Utils.count b"
  and "(bit b (unat (0 :: 32 word))) = True \<longleftrightarrow> hackers_delight_Utils.count (b >> unat (1 :: 32 word)) = hackers_delight_Utils.count b - (1 :: 32 word)"
  sorry
end
