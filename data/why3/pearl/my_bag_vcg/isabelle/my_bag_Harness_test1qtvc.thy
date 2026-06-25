theory my_bag_Harness_test1qtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_NumOf" "Why3STD.map_Const" "./my_bag_Bag" "./my_bag_ResizableArraySpec" "./my_bag_BagImpl"
begin
consts fc :: "'a rarray \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> bool"
axiomatization where fc_def:   "fc r x i = True \<longleftrightarrow> my_bag_ResizableArraySpec.data r i = x"
  for r :: "'a rarray"
  and x :: "'a"
  and i :: "int"
theorem test1'vc:
  shows "True"
  sorry
end
