theory tables_IMapAndSet_lt_def
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
typedecl  t
consts balancing :: "nat"
axiomatization where balancing_def:   "int balancing = int (0 :: nat) + (1 :: int)"
theorem lt_def:
  fixes x :: "int"
  fixes y :: "int"
  shows "x < y \<longleftrightarrow> x \<le> y \<and> \<not>y \<le> x"
  sorry
end
