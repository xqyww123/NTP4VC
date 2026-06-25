theory counting_sort_Spec
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_NumOf" "Why3STD.array_IntArraySorted"
begin
consts k :: "int"
axiomatization where k_def:   "(0 :: int) < k"
definition k_values :: "int list \<Rightarrow> _"
  where "k_values a \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length a) \<longrightarrow> (0 :: int) \<le> a ! nat i \<and> a ! nat i < k)" for a
consts fc :: "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool"
axiomatization where fc_def:   "fc a v k1 = True \<longleftrightarrow> a ! nat k1 = v"
  for a :: "int list"
  and v :: "int"
  and k1 :: "int"
definition numeq :: "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "numeq a v i j = numof (fc a v) i j" for a v i j
consts fc1 :: "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool"
axiomatization where fc1_def:   "fc1 a v k1 = True \<longleftrightarrow> a ! nat k1 < v"
  for a :: "int list"
  and v :: "int"
  and k1 :: "int"
definition numlt :: "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "numlt a v i j = numof (fc1 a v) i j" for a v i j
definition permut :: "int list \<Rightarrow> int list \<Rightarrow> _"
  where "permut a b \<longleftrightarrow> length a = length b \<and> (\<forall>(v :: int). (0 :: int) \<le> v \<and> v < k \<longrightarrow> numeq a v (0 :: int) (int (length a)) = numeq b v (0 :: int) (int (length b)))" for a b
end
