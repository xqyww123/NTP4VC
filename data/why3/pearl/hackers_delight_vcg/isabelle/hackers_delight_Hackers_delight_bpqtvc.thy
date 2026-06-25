theory hackers_delight_Hackers_delight_bpqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.int_NumOf" "./hackers_delight_Utils"
begin
definition validAscii :: "32 word \<Rightarrow> _"
  where "validAscii b \<longleftrightarrow> (bit (hackers_delight_Utils.count b) (unat (0 :: 32 word))) = False" for b
definition toGray :: "32 word \<Rightarrow> 32 word"
  where "toGray bv = bv XOR (bv >> unat (1 :: 32 word))" for bv
definition fromGray :: "32 word \<Rightarrow> 32 word"
  where "fromGray gr = (let b :: 32 word = gr XOR (gr >> unat (1 :: 32 word)); b1 :: 32 word = b XOR (b >> unat (2 :: 32 word)); b2 :: 32 word = b1 XOR (b1 >> unat (4 :: 32 word)); b3 :: 32 word = b2 XOR (b2 >> unat (8 :: 32 word)) in b3 XOR (b3 >> unat (16 :: 32 word)))" for gr
definition addDontOverflow :: "32 word \<Rightarrow> 32 word \<Rightarrow> _"
  where "addDontOverflow a b \<longleftrightarrow> b \<le> b + a \<and> a \<le> b + a" for a b
theorem bp'vc:
  fixes a :: "32 word"
  fixes x :: "32 word"
  fixes b :: "32 word"
  fixes c :: "32 word"
  fixes y :: "32 word"
  fixes d :: "32 word"
  assumes fact0: "a \<le> x"
  assumes fact1: "x \<le> b"
  assumes fact2: "c \<le> y"
  assumes fact3: "y \<le> d"
  assumes fact4: "addDontOverflow b d"
  shows "hackers_delight_Utils.max a c \<le> x OR y"
  and "x OR y \<le> b + d"
  and "(0 :: 32 word) \<le> x AND y"
  and "x AND y \<le> hackers_delight_Utils.min b d"
  and "(0 :: 32 word) \<le> x XOR y"
  and "x XOR y \<le> b + d"
  and "not b \<le> not x"
  and "not x \<le> not a"
  sorry
end
