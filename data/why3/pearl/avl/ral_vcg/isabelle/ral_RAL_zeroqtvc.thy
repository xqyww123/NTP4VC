theory ral_RAL_zeroqtvc
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
consts agg :: "('a \<Rightarrow> int) \<Rightarrow> 'a list \<Rightarrow> int"
axiomatization where agg'def:   "if int (length s) = (0 :: int) then agg f s = (0 :: int) else agg f s = f (s ! (0 :: nat)) + agg f (drop (1 :: nat) s)"
  for s :: "'a list"
  and f :: "'a \<Rightarrow> int"
theorem zero'vc:
  shows "True"
  sorry
end
