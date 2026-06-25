theory counting_sort_Spec_eqltqtvc
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
theorem eqlt'vc:
  fixes a :: "int list"
  fixes v :: "int"
  fixes l :: "int"
  fixes u :: "int"
  assumes fact0: "k_values a"
  assumes fact1: "(0 :: int) \<le> v"
  assumes fact2: "v < k"
  assumes fact3: "(0 :: int) \<le> l"
  assumes fact4: "l < u"
  assumes fact5: "u \<le> int (length a)"
  shows "numlt a v l u + numeq a v l u = numlt a (v + (1 :: int)) l u"
  sorry
end
