theory rightmostbittrick_Rmbt_rightmost_position_setqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref"
begin
theorem rightmost_position_set'vc:
  fixes a :: "64 word"
  assumes fact0: "\<not>a = (0 :: 64 word)"
  shows "bv_eq_sub_bv a (0 :: 64 word) (0 :: 64 word) (0 :: 64 word)"
  and "\<forall>(i :: 64 word). bv_eq_sub_bv a (0 :: 64 word) (0 :: 64 word) i \<longrightarrow> (\<forall>(o1 :: bool). (if i < (64 :: 64 word) then o1 = (if (bit a (unat i)) = True then False else True) else o1 = False) \<longrightarrow> (if o1 = True then ((0 :: int) \<le> (64 :: int) - uint i \<and> (64 :: int) - uint (i + (1 :: 64 word)) < (64 :: int) - uint i) \<and> bv_eq_sub_bv a (0 :: 64 word) (0 :: 64 word) (i + (1 :: 64 word)) else i < (64 :: 64 word) \<and> bv_eq_sub_bv a (0 :: 64 word) (0 :: 64 word) i \<and> (bit a (unat i)) = True))"
  sorry
end
