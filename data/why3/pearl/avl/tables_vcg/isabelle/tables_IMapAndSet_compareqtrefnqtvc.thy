theory tables_IMapAndSet_compareqtrefnqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
typedecl  t
consts balancing :: "nat"
axiomatization where balancing_def:   "int balancing = int (0 :: nat) + (1 :: int)"
theorem compare'refn'vc:
  fixes x :: "int"
  fixes y :: "int"
  shows "let result :: int = x - y in ((0 :: int) < result \<longleftrightarrow> y < x) \<and> (result < (0 :: int) \<longleftrightarrow> x < y) \<and> (result = (0 :: int) \<longleftrightarrow> x = y)"
  sorry
end
