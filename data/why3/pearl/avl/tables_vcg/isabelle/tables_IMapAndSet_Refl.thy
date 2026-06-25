theory tables_IMapAndSet_Refl
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
typedecl  t
consts balancing :: "nat"
axiomatization where balancing_def:   "int balancing = int (0 :: nat) + (1 :: int)"
theorem Refl:
  fixes x :: "int"
  shows "x \<le> x"
  sorry
end
