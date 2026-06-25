theory tables_IMapAndSet_balancingqtrefnqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
typedecl  t
consts balancing :: "nat"
axiomatization where balancing_def:   "int balancing = int (0 :: nat) + (1 :: int)"
theorem balancing'refn'vc:
  shows "(0 :: int) < int balancing"
  sorry
end
