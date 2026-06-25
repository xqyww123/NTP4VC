theory bitwalker_Bitwalker_peek_8bit_bvqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref" "mach.bv_BVCheck8" "mach.bv_BVCheck32" "mach.bv_BVCheck64"
begin
definition nth8_stream :: "8 word list \<Rightarrow> int \<Rightarrow> bool"
  where "nth8_stream stream pos = ((0 \<le> ((7 :: int) - pos emod (8 :: int)) \<and> bit (stream ! nat (pos ediv (8 :: int))) (nat ((7 :: int) - pos emod (8 :: int)))))" for stream pos
definition maxvalue :: "32 word \<Rightarrow> 64 word"
  where "maxvalue len = (1 :: 64 word) << unat (u32_to_u64 len)" for len
theorem peek_8bit_bv'vc:
  fixes left1 :: "32 word"
  fixes byte :: "8 word"
  assumes fact0: "(0 :: int) \<le> uint left1"
  assumes fact1: "uint left1 < (8 :: int)"
  shows "uint left1 \<le> (7 :: int) \<or> (7 :: 32 word) \<ge> left1"
  and "let o1 :: 32 word = (7 :: 32 word) - left1 in uint o1 = (7 :: int) - uint left1 \<longrightarrow> (if u8_to_u32 byte AND ((1 :: 32 word) << unat o1) = (0 :: 32 word) then False else True) = (bit byte (unat ((7 :: 8 word) - u32_to_u8 left1)))"
  and "(bit byte (unat ((7 :: 8 word) - u32_to_u8 left1))) = ((0 \<le> ((7 :: int) - uint left1) \<and> bit byte (nat ((7 :: int) - uint left1))))"
  sorry
end
