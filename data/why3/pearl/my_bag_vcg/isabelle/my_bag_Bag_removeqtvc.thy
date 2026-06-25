theory my_bag_Bag_removeqtvc
  imports "NTP4Verif.NTP4Verif"
begin
typedecl 'a bag
definition infix_eqeq :: "('a \<Rightarrow> int) \<Rightarrow> ('a \<Rightarrow> int) \<Rightarrow> _"
  where "infix_eqeq b1 b2 \<longleftrightarrow> (\<forall>(x :: 'a). b1 x = b2 x)" for b1 b2
consts add :: "'a \<Rightarrow> ('a \<Rightarrow> int) \<Rightarrow> 'a \<Rightarrow> int"
axiomatization where add_def:   "add e b x = (if x = e then b x + (1 :: int) else b x)"
  for e :: "'a"
  and b :: "'a \<Rightarrow> int"
  and x :: "'a"
theorem remove'vc:
  shows "True"
  sorry
end
