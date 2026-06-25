theory proper_cuts_ProperCut_consqtvc
  imports "NTP4Verif.NTP4Verif"
begin
definition injective :: "('a \<Rightarrow> 'b) \<Rightarrow> _"
  where "injective f \<longleftrightarrow> (\<forall>(x :: 'a) (x' :: 'a). \<not>x = x' \<longrightarrow> \<not>f x = f x')" for f
fun map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list"
  where "map f (Nil :: 'a list) = (Nil :: 'b list)" for f
      | "map f (Cons x s) = Cons (f x) (map f s)" for f x s
axiomatization where map'spec'0:   "y \<in> set (map f l) \<longleftrightarrow> (\<exists>(x :: 'a). x \<in> set l \<and> y = f x)"
  for y :: "'b"
  and f :: "'a \<Rightarrow> 'b"
  and l :: "'a list"
axiomatization where map'spec:   "distinct (map f l)"
 if "distinct l"
 and "injective f"
  for l :: "'a list"
  and f :: "'a \<Rightarrow> 'b"
definition cut :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> _"
  where "cut l1 l2 l \<longleftrightarrow> l1 @ l2 = l" for l1 l2 l
typedecl 'a cut_list
definition proper_cuts :: "('a list \<times> 'a list) list \<Rightarrow> 'a list \<Rightarrow> _"
  where "proper_cuts c l \<longleftrightarrow> distinct c \<and> (\<forall>(l1 :: 'a list) (l2 :: 'a list). (l1, l2) \<in> set c \<longleftrightarrow> cut l1 l2 l)" for c l
consts f :: "'a \<Rightarrow> 'a list \<times> 'a list \<Rightarrow> 'a list \<times> 'a list"
axiomatization where f_def:   "f x l = (case l of (l1, l2) \<Rightarrow> (Cons x l1, l2))"
  for x :: "'a"
  and l :: "'a list \<times> 'a list"
theorem cons'vc:
  fixes x :: "'a"
  shows "let f1 :: 'a list \<times> 'a list \<Rightarrow> 'a list \<times> 'a list = f x in injective f1 \<and> (\<forall>(l :: ('a list \<times> 'a list) list) (l1 :: 'a list) (l2 :: 'a list). (l1, l2) \<in> set (map f1 l) \<longleftrightarrow> (\<exists>(s1 :: 'a list). l1 = Cons x s1 \<and> (s1, l2) \<in> set l))"
  sorry
end
