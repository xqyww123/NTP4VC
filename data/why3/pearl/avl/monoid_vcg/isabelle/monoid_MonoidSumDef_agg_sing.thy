theory monoid_MonoidSumDef_agg_sing
  imports "NTP4Verif.NTP4Verif"
begin
typedecl  t
consts zero :: "t"
consts op :: "t \<Rightarrow> t \<Rightarrow> t"
axiomatization where assoc:   "op a (op b c) = op (op a b) c"
  for a :: "t"
  and b :: "t"
  and c :: "t"
axiomatization where neutral'0:   "op x zero = x"
  for x :: "t"
axiomatization where neutral'1:   "x = op zero x"
  for x :: "t"
consts agg :: "('a \<Rightarrow> t) \<Rightarrow> 'a list \<Rightarrow> t"
axiomatization where agg_def:   "if int (length s) = (0 :: int) then agg f s = zero else agg f s = op (f (s ! (0 :: nat))) (agg f (drop (1 :: nat) s))"
  for s :: "'a list"
  and f :: "'a \<Rightarrow> t"
theorem agg_sing:
  fixes s :: "'a list"
  fixes f :: "'a \<Rightarrow> t"
  assumes fact0: "int (length s) = (1 :: int)"
  shows "agg f s = f (s ! (0 :: nat))"
  sorry
end
