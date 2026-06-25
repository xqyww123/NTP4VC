theory bitwalker_Bitwalker_poke_64bit_bvqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref" "mach.bv_BVCheck8" "mach.bv_BVCheck32" "mach.bv_BVCheck64"
begin
definition nth8_stream :: "8 word list \<Rightarrow> int \<Rightarrow> bool"
  where "nth8_stream stream pos = ((0 \<le> ((7 :: int) - pos emod (8 :: int)) \<and> bit (stream ! nat (pos ediv (8 :: int))) (nat ((7 :: int) - pos emod (8 :: int)))))" for stream pos
definition maxvalue :: "32 word \<Rightarrow> 64 word"
  where "maxvalue len = (1 :: 64 word) << unat (u32_to_u64 len)" for len
theorem poke_64bit_bv'vc:
  fixes left1 :: "32 word"
  fixes flag :: "bool"
  fixes "value" :: "64 word"
  assumes fact0: "uint left1 < (64 :: int)"
  shows "uint left1 \<le> (63 :: int) \<or> (63 :: 32 word) \<ge> left1"
  and "let o1 :: 32 word = (63 :: 32 word) - left1 in uint o1 = (63 :: int) - uint left1 \<longrightarrow> (let mask :: 64 word = (1 :: 64 word) << unat (u32_to_u64 o1) in (case flag of True \<Rightarrow> True | False \<Rightarrow> True) \<and> (\<forall>(result :: 64 word). (case flag of True \<Rightarrow> result = value OR mask | False \<Rightarrow> result = value AND not mask) \<longrightarrow> (\<forall>(i :: 32 word). \<not>i = (63 :: 32 word) - left1 \<longrightarrow> (bit result (unat (u32_to_u64 i))) = (bit value (unat (u32_to_u64 i)))) \<and> flag = (bit result (unat (u32_to_u64 ((63 :: 32 word) - left1))))))"
  and "\<forall>(result :: 64 word). (\<forall>(i :: 32 word). \<not>i = (63 :: 32 word) - left1 \<longrightarrow> (bit result (unat (u32_to_u64 i))) = (bit value (unat (u32_to_u64 i)))) \<and> flag = (bit result (unat (u32_to_u64 ((63 :: 32 word) - left1)))) \<longrightarrow> (\<forall>(i :: int). ((0 :: int) \<le> i \<and> i < (64 :: int)) \<and> \<not>i = (63 :: int) - uint left1 \<longrightarrow> ((0 \<le> i \<and> bit result (nat i))) = ((0 \<le> i \<and> bit value (nat i)))) \<and> flag = ((0 \<le> ((63 :: int) - uint left1) \<and> bit result (nat ((63 :: int) - uint left1))))"
  sorry
end
