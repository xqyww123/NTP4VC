theory hackers_delight_Hackers_delight_asciiPropqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.int_NumOf" "./hackers_delight_Utils"
begin
definition validAscii :: "32 word \<Rightarrow> _"
  where "validAscii b \<longleftrightarrow> (bit (hackers_delight_Utils.count b) (unat (0 :: 32 word))) = False" for b
theorem asciiProp'vc:
  fixes a :: "32 word"
  fixes b :: "32 word"
  shows "validAscii a \<and> \<not>validAscii b \<or> validAscii b \<and> \<not>validAscii a \<longleftrightarrow> (bit (hammingD a b) (unat (0 :: 32 word))) = True"
  sorry
end
