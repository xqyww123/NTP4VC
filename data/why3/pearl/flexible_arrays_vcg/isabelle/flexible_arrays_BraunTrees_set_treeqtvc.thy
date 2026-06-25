theory flexible_arrays_BraunTrees_set_treeqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.bintree_Tree" "Why3STD.bintree_Size"
begin
fun braun :: "'a tree \<Rightarrow> _"
  where "braun (Empty :: 'a tree) = True"
      | "braun (Node l x r) = ((bintree_Size.size l = bintree_Size.size r \<or> bintree_Size.size l = bintree_Size.size r + (1 :: int)) \<and> braun l \<and> braun r)" for l x r
consts get_tree :: "'a tree \<Rightarrow> int \<Rightarrow> 'a"
axiomatization where get_tree_def:   "case t of (Empty :: 'a tree) \<Rightarrow> False | Node l x r \<Rightarrow> (if i = (0 :: int) then get_tree t i = x else if i cmod (2 :: int) = (1 :: int) then get_tree t i = get_tree l (i cdiv (2 :: int)) else get_tree t i = get_tree r (i cdiv (2 :: int) - (1 :: int)))"
 if "(0 :: int) \<le> i"
 and "i < bintree_Size.size t"
 and "braun t"
  for i :: "int"
  and t :: "'a tree"
theorem set_tree'vc:
  fixes i :: "int"
  fixes t :: "'a tree"
  fixes v :: "'a"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "i < bintree_Size.size t"
  assumes fact2: "braun t"
  shows "case t of (Empty :: 'a tree) \<Rightarrow> False | Node l x r \<Rightarrow> \<not>i = (0 :: int) \<longrightarrow> \<not>(2 :: int) = (0 :: int) \<and> (if i cmod (2 :: int) = (1 :: int) then \<not>(2 :: int) = (0 :: int) \<and> (let o1 :: int = i cdiv (2 :: int) in (case t of (Empty :: 'a tree) \<Rightarrow> False | Node f _ f1 \<Rightarrow> f = l \<or> f1 = l) \<and> ((0 :: int) \<le> o1 \<and> o1 < bintree_Size.size l) \<and> braun l) else \<not>(2 :: int) = (0 :: int) \<and> (let o1 :: int = i cdiv (2 :: int) - (1 :: int) in (case t of (Empty :: 'a tree) \<Rightarrow> False | Node f _ f1 \<Rightarrow> f = r \<or> f1 = r) \<and> ((0 :: int) \<le> o1 \<and> o1 < bintree_Size.size r) \<and> braun r))"
  and "\<forall>(r :: 'a tree). (case t of (Empty :: 'a tree) \<Rightarrow> False | Node l x r1 \<Rightarrow> (if i = (0 :: int) then r = Node l v r1 else if i cmod (2 :: int) = (1 :: int) then let o1 :: int = i cdiv (2 :: int) in \<exists>(o2 :: 'a tree). (bintree_Size.size o2 = bintree_Size.size l \<and> braun o2 \<and> get_tree o2 o1 = v \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < bintree_Size.size l \<longrightarrow> \<not>j = o1 \<longrightarrow> get_tree o2 j = get_tree l j)) \<and> r = Node o2 x r1 else let o1 :: int = i cdiv (2 :: int) - (1 :: int) in \<exists>(o2 :: 'a tree). (bintree_Size.size o2 = bintree_Size.size r1 \<and> braun o2 \<and> get_tree o2 o1 = v \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < bintree_Size.size r1 \<longrightarrow> \<not>j = o1 \<longrightarrow> get_tree o2 j = get_tree r1 j)) \<and> r = Node l x o2)) \<longrightarrow> bintree_Size.size r = bintree_Size.size t \<and> braun r \<and> get_tree r i = v \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < bintree_Size.size t \<longrightarrow> \<not>j = i \<longrightarrow> get_tree r j = get_tree t j)"
  sorry
end
