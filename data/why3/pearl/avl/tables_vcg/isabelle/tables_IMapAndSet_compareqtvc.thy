theory tables_IMapAndSet_compareqtvc
  imports "NTP4Verif.NTP4Verif"
begin
typedecl  t
consts balancing :: "nat"
axiomatization where balancing_def:   "int balancing = int (0 :: nat) + (1 :: int)"
theorem compare'vc:
  shows "True"
  sorry
end
