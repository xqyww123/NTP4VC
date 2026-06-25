theory tables_IMapAndSet_Trans
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
typedecl  t
consts balancing :: "nat"
axiomatization where balancing_def:   "int balancing = int (0 :: nat) + (1 :: int)"
theorem Trans:
  fixes x :: "int"
  fixes y :: "int"
  fixes z :: "int"
  assumes fact0: "x \<le> y"
  assumes fact1: "y \<le> z"
  shows "x \<le> z"
  sorry
end
