theory ral_RAL_neutral1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_avl_lib.avl_SelectionTypes"
begin
consts balancing :: "nat"
axiomatization where balancing'def:   "(0 :: int) < int balancing"
typedecl  m
typedecl  t
axiomatization where assoc:   "a + (b + c) = a + b + c"
  for a :: "int"
  and b :: "int"
  and c :: "int"
axiomatization where neutral'0:   "x + (0 :: int) = x"
  for x :: "int"
axiomatization where neutral'1:   "x = (0 :: int) + x"
  for x :: "int"
theorem neutral1:
  fixes x :: "int"
  shows "x + (0 :: int) = x"
  and "x = (0 :: int) + x"
  sorry
end
