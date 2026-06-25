theory verifythis_2021_lexicographic_permutations_1_Top_all_permutationsqtvc
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
consts cons_closure :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
axiomatization where cons_closure_def:   "cons_closure y y1 = Cons y y1"
  for y :: "'a"
  and y1 :: "'a list"
theorem all_permutations'vc:
  fixes s :: "int list"
  shows "let n :: int = int (length s) in (\<forall>(k :: int). (0 :: int) \<le> k \<and> k \<le> n \<longrightarrow> (if k = (0 :: int) then \<forall>(p :: int list). int (length p) = k \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < k \<longrightarrow> (0 :: int) < occ_all (p ! nat i) s) \<longrightarrow> p |\<in>| finsert [] fempty else let o1 :: int = k - (1 :: int) in (((0 :: int) \<le> k \<and> o1 < k) \<and> (0 :: int) \<le> o1 \<and> o1 \<le> n) \<and> (\<forall>(now :: int list fset). (\<forall>(p :: int list). int (length p) = o1 \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < o1 \<longrightarrow> (0 :: int) < occ_all (p ! nat i) s) \<longrightarrow> p |\<in>| now) \<longrightarrow> (let o2 :: int = n - (1 :: int) in ((0 :: int) \<le> o2 + (1 :: int) \<longrightarrow> (\<forall>(p :: int list). int (length p) = k \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < k \<longrightarrow> (0 :: int) < occ_all (p ! nat i) s) \<and> (0 :: int) < occ (p ! (0 :: nat)) s (0 :: int) (0 :: int) \<longrightarrow> p |\<in>| fempty) \<and> (\<forall>(acc :: int list fset). (\<forall>(j :: int). ((0 :: int) \<le> j \<and> j \<le> o2) \<and> (\<forall>(p :: int list). int (length p) = k \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < k \<longrightarrow> (0 :: int) < occ_all (p ! nat i) s) \<and> (0 :: int) < occ (p ! (0 :: nat)) s (0 :: int) j \<longrightarrow> p |\<in>| acc) \<longrightarrow> (let o3 :: int = s ! nat j; o4 :: int list \<Rightarrow> int list = cons_closure o3 in (\<forall>(s1 :: int list). int (length (o4 s1)) = (1 :: int) + int (length s1)) \<and> (\<forall>(s1 :: int list). o4 s1 ! (0 :: nat) = o3) \<and> (\<forall>(s1 :: int list) (i :: int). (0 :: int) < i \<and> i \<le> int (length s1) \<longrightarrow> o4 s1 ! nat i = s1 ! nat (i - (1 :: int))) \<longrightarrow> (\<forall>(p :: int list). int (length p) = k \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < k \<longrightarrow> (0 :: int) < occ_all (p ! nat i) s) \<and> (0 :: int) < occ (p ! (0 :: nat)) s (0 :: int) (j + (1 :: int)) \<longrightarrow> p |\<in>| acc |\<union>| o4 |`| now))) \<and> ((\<forall>(p :: int list). int (length p) = k \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < k \<longrightarrow> (0 :: int) < occ_all (p ! nat i) s) \<and> (0 :: int) < occ (p ! (0 :: nat)) s (0 :: int) (o2 + (1 :: int)) \<longrightarrow> p |\<in>| acc) \<longrightarrow> (\<forall>(p :: int list). int (length p) = k \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < k \<longrightarrow> (0 :: int) < occ_all (p ! nat i) s) \<longrightarrow> p |\<in>| acc)))) \<and> (o2 + (1 :: int) < (0 :: int) \<longrightarrow> (\<forall>(p :: int list). int (length p) = k \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < k \<longrightarrow> (0 :: int) < occ_all (p ! nat i) s) \<longrightarrow> p |\<in>| fempty)))))) \<and> ((0 :: int) \<le> n \<and> n \<le> n) \<and> (\<forall>(all1 :: int list fset). (\<forall>(p :: int list). int (length p) = n \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n \<longrightarrow> (0 :: int) < occ_all (p ! nat i) s) \<longrightarrow> p |\<in>| all1) \<longrightarrow> (\<forall>(p :: int list). is_permutation_of p s \<longrightarrow> p |\<in>| all1))"
  sorry
end
