theory tree_of_array_TreeOfArray_tree_of_array_auxqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.bintree_Tree" "Why3STD.bintree_Size" "Why3STD.bintree_Height" "Why3STD.bintree_Inorder"
begin
theorem tree_of_array_aux'vc:
  fixes lo :: "int"
  fixes hi :: "int"
  fixes a :: "'a list"
  assumes fact0: "(0 :: int) \<le> lo"
  assumes fact1: "lo \<le> hi"
  assumes fact2: "hi \<le> int (length a)"
  shows "\<not>hi = lo \<longrightarrow> \<not>(2 :: int) = (0 :: int) \<and> (let mid :: int = lo + (hi - lo) cdiv (2 :: int) in (((0 :: int) \<le> hi - lo \<and> mid - lo < hi - lo) \<and> (0 :: int) \<le> lo \<and> lo \<le> mid \<and> mid \<le> int (length a)) \<and> (\<forall>(left1 :: 'a tree). (let n :: int = mid - lo in bintree_Size.size left1 = n \<and> inorder left1 = take (nat mid - nat lo) (drop (nat lo) a) \<and> ((0 :: int) < n \<longrightarrow> (let h :: int = height left1 in (2 :: int) ^\<^sub>i (h - (1 :: int)) \<le> n \<and> n < (2 :: int) ^\<^sub>i h))) \<longrightarrow> (let o1 :: int = mid + (1 :: int) in (((0 :: int) \<le> hi - lo \<and> hi - o1 < hi - lo) \<and> (0 :: int) \<le> o1 \<and> o1 \<le> hi \<and> hi \<le> int (length a)) \<and> (\<forall>(right1 :: 'a tree). (let n :: int = hi - o1 in bintree_Size.size right1 = n \<and> inorder right1 = take (nat hi - nat o1) (drop (nat o1) a) \<and> ((0 :: int) < n \<longrightarrow> (let h :: int = height right1 in (2 :: int) ^\<^sub>i (h - (1 :: int)) \<le> n \<and> n < (2 :: int) ^\<^sub>i h))) \<longrightarrow> (0 :: int) \<le> mid \<and> mid < int (length a)))))"
  and "\<forall>(result :: 'a tree). (if hi = lo then result = (Empty :: 'a tree) else let mid :: int = lo + (hi - lo) cdiv (2 :: int) in \<exists>(left1 :: 'a tree). (let n :: int = mid - lo in bintree_Size.size left1 = n \<and> inorder left1 = take (nat mid - nat lo) (drop (nat lo) a) \<and> ((0 :: int) < n \<longrightarrow> (let h :: int = height left1 in (2 :: int) ^\<^sub>i (h - (1 :: int)) \<le> n \<and> n < (2 :: int) ^\<^sub>i h))) \<and> (let o1 :: int = mid + (1 :: int) in \<exists>(right1 :: 'a tree). (let n :: int = hi - o1 in bintree_Size.size right1 = n \<and> inorder right1 = take (nat hi - nat o1) (drop (nat o1) a) \<and> ((0 :: int) < n \<longrightarrow> (let h :: int = height right1 in (2 :: int) ^\<^sub>i (h - (1 :: int)) \<le> n \<and> n < (2 :: int) ^\<^sub>i h))) \<and> result = Node left1 (a ! nat mid) right1)) \<longrightarrow> (let n :: int = hi - lo in bintree_Size.size result = n \<and> inorder result = take (nat hi - nat lo) (drop (nat lo) a) \<and> ((0 :: int) < n \<longrightarrow> (let h :: int = height result in (2 :: int) ^\<^sub>i (h - (1 :: int)) \<le> n \<and> n < (2 :: int) ^\<^sub>i h)))"
  sorry
end
