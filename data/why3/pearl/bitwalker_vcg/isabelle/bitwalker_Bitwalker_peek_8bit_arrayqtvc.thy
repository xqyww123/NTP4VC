theory bitwalker_Bitwalker_peek_8bit_arrayqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref" "mach.bv_BVCheck8" "mach.bv_BVCheck32" "mach.bv_BVCheck64"
begin
definition nth8_stream :: "8 word list \<Rightarrow> int \<Rightarrow> bool"
  where "nth8_stream stream pos = ((0 \<le> ((7 :: int) - pos emod (8 :: int)) \<and> bit (stream ! nat (pos ediv (8 :: int))) (nat ((7 :: int) - pos emod (8 :: int)))))" for stream pos
definition maxvalue :: "32 word \<Rightarrow> 64 word"
  where "maxvalue len = (1 :: 64 word) << unat (u32_to_u64 len)" for len
theorem peek_8bit_array'vc:
  fixes addr :: "8 word list"
  fixes left1 :: "32 word"
  assumes fact0: "(8 :: int) * int (length addr) < (4294967296 :: int)"
  assumes fact1: "uint left1 < (8 :: int) * int (length addr)"
  shows "\<not>(8 :: 32 word) = (0 :: 32 word) \<or> \<not>(8 :: int) = (0 :: int)"
  and "uint (left1 mod (8 :: 32 word)) = uint left1 emod (8 :: int) \<longrightarrow> (\<not>(8 :: 32 word) = (0 :: 32 word) \<or> \<not>(8 :: int) = (0 :: int)) \<and> (uint (left1 div (8 :: 32 word)) = uint left1 ediv (8 :: int) \<longrightarrow> (let o1 :: int = uint (left1 div (8 :: 32 word)) in ((0 :: int) \<le> o1 \<and> o1 < int (length addr)) \<and> ((0 :: int) \<le> uint (left1 mod (8 :: 32 word)) \<and> uint (left1 mod (8 :: 32 word)) < (8 :: int)) \<and> ((0 \<le> ((7 :: int) - uint (left1 mod (8 :: 32 word))) \<and> bit (addr ! nat o1) (nat ((7 :: int) - uint (left1 mod (8 :: 32 word)))))) = nth8_stream addr (uint left1)))"
  sorry
end
