theory ral_RAL_assoc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_avl_lib.avl_SelectionTypes"
begin
consts balancing :: "nat"
axiomatization where balancing'def:   "(0 :: int) < int balancing"
typedecl  m
typedecl  t
theorem assoc:
  fixes a :: "int"
  fixes b :: "int"
  fixes c :: "int"
  shows "a + (b + c) = a + b + c"
  sorry
end
