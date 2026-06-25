theory flexible_arrays_FlexibleArrays_consqtvc
  imports "NTP4Verif.NTP4Verif" "./flexible_arrays_BraunTrees" "Why3STD.bintree_Tree" "Why3STD.bintree_Size"
begin
typedecl 'a t
consts size :: "'a t \<Rightarrow> int"
consts tree :: "'a t \<Rightarrow> 'a tree"
axiomatization where t'invariant'0:   "braun (tree self)"
  for self :: "'a t"
axiomatization where t'invariant'1:   "bintree_Size.size (tree self) = size self"
  for self :: "'a t"
axiomatization where t'invariant'2:   "(0 :: int) \<le> size self"
  for self :: "'a t"
definition t'eq :: "'a t \<Rightarrow> 'a t \<Rightarrow> _"
  where "t'eq a b \<longleftrightarrow> size a = size b \<and> tree a = tree b" for a b
axiomatization where t'inj:   "a = b"
 if "t'eq a b"
  for a :: "'a t"
  and b :: "'a t"
consts empty :: "'a t"
axiomatization where size_def:   "size (empty :: 'a t) = (0 :: int)"
consts get :: "'a t \<Rightarrow> int \<Rightarrow> 'a"
axiomatization where get_def:   "get t1 i = get_tree (tree t1) i"
 if "(0 :: int) \<le> i"
 and "i < size t1"
  for i :: "int"
  and t1 :: "'a t"
theorem cons'vc:
  fixes t1 :: "'a t"
  fixes v :: "'a"
  shows "let o1 :: 'a tree = tree t1 in braun o1 \<and> (\<forall>(o2 :: 'a tree). bintree_Size.size o2 = bintree_Size.size o1 + (1 :: int) \<and> braun o2 \<and> get_tree o2 (0 :: int) = v \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < bintree_Size.size o1 \<longrightarrow> get_tree o2 (i + (1 :: int)) = get_tree o1 i) \<longrightarrow> (let o3 :: int = size t1 + (1 :: int) in (braun o2 \<and> bintree_Size.size o2 = o3 \<and> (0 :: int) \<le> o3) \<and> (\<forall>(r :: 'a t). size r = o3 \<and> tree r = o2 \<longrightarrow> size r = size t1 + (1 :: int) \<and> get r (0 :: int) = v \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < size t1 \<longrightarrow> get r (i + (1 :: int)) = get t1 i))))"
  sorry
end
