theory bitcount_AsciiCode_bv_evenqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref" "Why3STD.int_NumOf" "./bitcount_BitCounting32" "mach.bv_BVCheck32"
begin
definition validAscii :: "32 word \<Rightarrow> _"
  where "validAscii b \<longleftrightarrow> even (count_logic b)" for b
theorem bv_even'vc:
  fixes b :: "32 word"
  shows "even (uint b) \<longleftrightarrow> \<not>(bit b (0 :: nat)) = True"
  sorry
end
