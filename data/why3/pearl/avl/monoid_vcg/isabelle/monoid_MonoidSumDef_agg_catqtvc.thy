theory monoid_MonoidSumDef_agg_catqtvc
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
theorem agg_cat'vc:
  fixes f :: "'a \<Rightarrow> t"
  fixes s1 :: "'a list"
  fixes s2 :: "'a list"
  shows "agg f (s1 @ s2) = op (agg f s1) (agg f s2)"
  sorry
end
