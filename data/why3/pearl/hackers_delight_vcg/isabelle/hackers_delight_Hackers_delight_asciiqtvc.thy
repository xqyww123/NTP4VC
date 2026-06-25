theory hackers_delight_Hackers_delight_asciiqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.int_NumOf" "./hackers_delight_Utils"
begin
definition validAscii :: "32 word \<Rightarrow> _"
  where "validAscii b \<longleftrightarrow> (bit (hackers_delight_Utils.count b) (unat (0 :: 32 word))) = False" for b
theorem ascii'vc:
  fixes b :: "32 word"
  assumes fact0: "\<not>(bit b (unat (31 :: 32 word))) = True"
  shows "validAscii (b OR (hackers_delight_Utils.count b << unat (31 :: 32 word)))"
  sorry
end
