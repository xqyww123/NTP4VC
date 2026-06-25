theory flexible_arrays_FlexibleArrays_getqtvc
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
theorem get'vc:
  fixes i :: "int"
  fixes t1 :: "'a t"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "i < size t1"
  shows "let o1 :: 'a tree = tree t1 in ((0 :: int) \<le> i \<and> i < bintree_Size.size o1) \<and> braun o1"
  sorry
end
