theory tables_IMapAndSet_Total
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
typedecl  t
consts balancing :: "nat"
axiomatization where balancing_def:   "int balancing = int (0 :: nat) + (1 :: int)"
theorem Total:
  fixes x :: "int"
  fixes y :: "int"
  shows "x \<le> y \<or> y \<le> x"
  sorry
end
