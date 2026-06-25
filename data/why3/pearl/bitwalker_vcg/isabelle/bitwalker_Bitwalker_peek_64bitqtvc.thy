theory bitwalker_Bitwalker_peek_64bitqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref" "mach.bv_BVCheck8" "mach.bv_BVCheck32" "mach.bv_BVCheck64"
begin
definition nth8_stream :: "8 word list \<Rightarrow> int \<Rightarrow> bool"
  where "nth8_stream stream pos = ((0 \<le> ((7 :: int) - pos emod (8 :: int)) \<and> bit (stream ! nat (pos ediv (8 :: int))) (nat ((7 :: int) - pos emod (8 :: int)))))" for stream pos
definition maxvalue :: "32 word \<Rightarrow> 64 word"
  where "maxvalue len = (1 :: 64 word) << unat (u32_to_u64 len)" for len
theorem peek_64bit'vc:
  fixes left1 :: "32 word"
  fixes "value" :: "64 word"
  assumes fact0: "uint left1 < (64 :: int)"
  shows "uint left1 \<le> (63 :: int) \<or> (63 :: 32 word) \<ge> left1"
  and "let o1 :: 32 word = (63 :: 32 word) - left1 in uint o1 = (63 :: int) - uint left1 \<longrightarrow> (if value AND ((1 :: 64 word) << unat (u32_to_u64 o1)) = (0 :: 64 word) then False else True) = (bit value (unat ((63 :: 64 word) - u32_to_u64 left1)))"
  and "(bit value (unat ((63 :: 64 word) - u32_to_u64 left1))) = ((0 \<le> ((63 :: int) - uint left1) \<and> bit value (nat ((63 :: int) - uint left1))))"
  sorry
end
