theory bitwalker_Bitwalker_nth64qtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref" "mach.bv_BVCheck8" "mach.bv_BVCheck32" "mach.bv_BVCheck64"
begin
definition nth8_stream :: "8 word list \<Rightarrow> int \<Rightarrow> bool"
  where "nth8_stream stream pos = ((0 \<le> ((7 :: int) - pos emod (8 :: int)) \<and> bit (stream ! nat (pos ediv (8 :: int))) (nat ((7 :: int) - pos emod (8 :: int)))))" for stream pos
theorem nth64'vc:
  fixes i :: "int"
  fixes "value" :: "64 word"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "i < (64 :: int)"
  shows "((0 \<le> i \<and> bit value (nat i))) = (bit value (unat (u32_to_u64 (w32_of_int i))))"
  sorry
end
