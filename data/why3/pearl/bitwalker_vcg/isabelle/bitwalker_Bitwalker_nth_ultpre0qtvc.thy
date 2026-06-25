theory bitwalker_Bitwalker_nth_ultpre0qtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref" "mach.bv_BVCheck8" "mach.bv_BVCheck32" "mach.bv_BVCheck64"
begin
definition nth8_stream :: "8 word list \<Rightarrow> int \<Rightarrow> bool"
  where "nth8_stream stream pos = ((0 \<le> ((7 :: int) - pos emod (8 :: int)) \<and> bit (stream ! nat (pos ediv (8 :: int))) (nat ((7 :: int) - pos emod (8 :: int)))))" for stream pos
definition maxvalue :: "32 word \<Rightarrow> 64 word"
  where "maxvalue len = (1 :: 64 word) << unat (u32_to_u64 len)" for len
theorem nth_ultpre0'vc:
  fixes len :: "32 word"
  fixes x :: "64 word"
  assumes fact0: "uint len < (64 :: int)"
  shows "bv_eq_sub x (0 :: 64 word) (uint len) ((64 :: int) - uint len) \<longleftrightarrow> uint x < uint (maxvalue len)"
  sorry
end
