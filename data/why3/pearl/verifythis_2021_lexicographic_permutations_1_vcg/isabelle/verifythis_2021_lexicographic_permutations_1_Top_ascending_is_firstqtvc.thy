theory verifythis_2021_lexicographic_permutations_1_Top_ascending_is_firstqtvc
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
theorem ascending_is_first'vc:
  fixes s :: "int list"
  fixes p :: "int list"
  assumes fact0: "ascending s (0 :: int) (int (length s))"
  assumes fact1: "is_permutation_of p s"
  shows "let o1 :: int = int (length s) - (1 :: int) in ((0 :: int) \<le> o1 + (1 :: int) \<longrightarrow> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < (0 :: int) \<longrightarrow> s ! nat j = p ! nat j) \<and> (\<forall>(i :: int). ((0 :: int) \<le> i \<and> i \<le> o1) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < i \<longrightarrow> s ! nat j = p ! nat j) \<longrightarrow> (if s ! nat i < p ! nat i then \<not>lt p s else if p ! nat i < s ! nat i then \<not>lt p s else \<forall>(j :: int). (0 :: int) \<le> j \<and> j < i + (1 :: int) \<longrightarrow> s ! nat j = p ! nat j)) \<and> ((\<forall>(j :: int). (0 :: int) \<le> j \<and> j < o1 + (1 :: int) \<longrightarrow> s ! nat j = p ! nat j) \<longrightarrow> \<not>lt p s)) \<and> (o1 + (1 :: int) < (0 :: int) \<longrightarrow> \<not>lt p s)"
  sorry
end
