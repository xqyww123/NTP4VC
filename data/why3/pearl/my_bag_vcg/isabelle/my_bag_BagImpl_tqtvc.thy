theory my_bag_BagImpl_tqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_NumOf" "Why3STD.map_Const" "./my_bag_Bag" "./my_bag_ResizableArraySpec"
begin
consts fc :: "'a rarray \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> bool"
axiomatization where fc_def:   "fc r x i = True \<longleftrightarrow> data r i = x"
  for r :: "'a rarray"
  and x :: "'a"
  and i :: "int"
definition numof :: "'a rarray \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "numof r x l u = int_NumOf.numof (fc r x) l u" for r x l u
consts fc1 :: "'a \<Rightarrow> int"
consts fc2 :: "'a \<Rightarrow> int"
axiomatization where fc1_def:   "fc1 y0 = (0 :: int)"
  for y0 :: "'a"
axiomatization where fc2_def:   "fc2 y0 = (0 :: int)"
  for y0 :: "'a"
theorem t'vc:
  fixes o2 :: "'a"
  shows "(0 :: int) \<le> (0 :: int)"
  and "\<forall>(o1 :: 'a rarray). len o1 = (0 :: int) \<and> data o1 = (const :: 'a \<Rightarrow> int \<Rightarrow> 'a) o2 \<longrightarrow> ((0 :: int) \<le> (0 :: int) \<and> (0 :: int) = len o1) \<and> ((0 :: int) \<le> (0 :: int) \<and> (0 :: int) = len o1 \<longrightarrow> (\<forall>(x :: 'a). fc2 x = numof o1 x (0 :: int) (0 :: int)))"
  sorry
end
