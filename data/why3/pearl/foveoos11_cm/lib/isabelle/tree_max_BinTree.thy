theory tree_max_BinTree
  imports "NTP4Verif.NTP4Verif"
begin
datatype  tree = Null | Tree "int" "tree" "tree"
fun mem :: "int \<Rightarrow> tree \<Rightarrow> _"
  where "mem v Null = False" for v
      | "mem v (Tree x l r) = (x = v \<or> mem v l \<or> mem v r)" for v x l r
fun ge_tree :: "int \<Rightarrow> tree \<Rightarrow> _"
  where "ge_tree v Null = True" for v
      | "ge_tree v (Tree x l r) = (x \<le> v \<and> ge_tree v l \<and> ge_tree v r)" for v x l r
end
