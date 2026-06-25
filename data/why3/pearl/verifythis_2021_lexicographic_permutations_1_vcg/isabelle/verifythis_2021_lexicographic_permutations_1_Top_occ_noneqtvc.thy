theory verifythis_2021_lexicographic_permutations_1_Top_occ_noneqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_NumOf"
begin
typedecl  elt
typedecl  permutation
definition lt :: "int list \<Rightarrow> int list \<Rightarrow> _"
  where "lt p q \<longleftrightarrow> (length p = length q \<and> (0 :: int) < int (length q)) \<and> (\<exists>(i :: int). ((0 :: int) \<le> i \<and> i < int (length p)) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < i \<longrightarrow> p ! nat j = q ! nat j) \<and> p ! nat i < q ! nat i)" for p q
consts iseq :: "'a \<Rightarrow> 'a list \<Rightarrow> int \<Rightarrow> bool"
axiomatization where iseq_def:   "iseq x s i = True \<longleftrightarrow> s ! nat i = x"
  for x :: "'a"
  and s :: "'a list"
  and i :: "int"
definition occ :: "'a \<Rightarrow> 'a list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "occ x s l u = numof (iseq x s) l u" for x s l u
definition occ_all :: "'a \<Rightarrow> 'a list \<Rightarrow> int"
  where "occ_all x s = occ x s (0 :: int) (int (length s))" for x s
definition is_permutation_of :: "int list \<Rightarrow> int list \<Rightarrow> _"
  where "is_permutation_of p a \<longleftrightarrow> length p = length a \<and> (\<forall>(x :: int). occ_all x p = occ_all x a)" for p a
definition descending :: "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "descending s lo hi \<longleftrightarrow> ((0 :: int) \<le> lo \<and> lo \<le> hi \<and> hi \<le> int (length s)) \<and> (\<forall>(i :: int) (j :: int). lo \<le> i \<and> i \<le> j \<and> j < hi \<longrightarrow> s ! nat j \<le> s ! nat i)" for s lo hi
definition ascending :: "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "ascending s lo hi \<longleftrightarrow> ((0 :: int) \<le> lo \<and> lo \<le> hi \<and> hi \<le> int (length s)) \<and> (\<forall>(i :: int) (j :: int). lo \<le> i \<and> i \<le> j \<and> j < hi \<longrightarrow> s ! nat i \<le> s ! nat j)" for s lo hi
consts to_seq :: "int list \<Rightarrow> int list"
axiomatization where to_seq'spec'0:   "length (to_seq a) = length a"
  for a :: "int list"
axiomatization where to_seq'spec:   "to_seq a ! nat i = a ! nat i"
 if "(0 :: int) \<le> i"
 and "i < int (length (to_seq a))"
  for i :: "int"
  and a :: "int list"
theorem occ_none'vc:
  fixes l :: "int"
  fixes u :: "int"
  fixes s :: "int list"
  fixes v :: "int"
  assumes fact0: "(0 :: int) \<le> l"
  assumes fact1: "l \<le> u"
  assumes fact2: "u \<le> int (length s)"
  assumes fact3: "\<forall>(k :: int). l \<le> k \<and> k < u \<longrightarrow> \<not>s ! nat k = v"
  shows "occ v s l u = (0 :: int)"
  sorry
end
