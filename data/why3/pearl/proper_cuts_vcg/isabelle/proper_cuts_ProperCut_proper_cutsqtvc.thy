theory proper_cuts_ProperCut_proper_cutsqtvc
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
consts cons :: "'a \<Rightarrow> 'a list \<times> 'a list \<Rightarrow> 'a list \<times> 'a list"
axiomatization where cons_def:   "cons x l = (case l of (l1, l2) \<Rightarrow> (Cons x l1, l2))"
  for x :: "'a"
  and l :: "'a list \<times> 'a list"
axiomatization where cons'spec'0:   "injective (cons x)"
  for x :: "'a"
axiomatization where cons'spec:   "(l1, l2) \<in> set (map (cons x) l) \<longleftrightarrow> (\<exists>(s1 :: 'a list). l1 = Cons x s1 \<and> (s1, l2) \<in> set l)"
  for l1 :: "'a list"
  and l2 :: "'a list"
  and x :: "'a"
  and l :: "('a list \<times> 'a list) list"
theorem proper_cuts'vc:
  fixes l :: "'a list"
  shows "case l of (Nil :: 'a list) \<Rightarrow> True | Cons x r \<Rightarrow> (case l of (Nil :: 'a list) \<Rightarrow> False | Cons _ f \<Rightarrow> f = r)"
  and "\<forall>(r :: ('a list \<times> 'a list) list). (case l of (Nil :: 'a list) \<Rightarrow> r = Cons ((Nil :: 'a list), (Nil :: 'a list)) (Nil :: ('a list \<times> 'a list) list) | Cons x r1 \<Rightarrow> (\<exists>(pr :: ('a list \<times> 'a list) list). proper_cuts pr r1 \<and> (let o1 :: 'a list \<times> 'a list \<Rightarrow> 'a list \<times> 'a list = cons x in (injective o1 \<and> (\<forall>(l1 :: ('a list \<times> 'a list) list) (l11 :: 'a list) (l2 :: 'a list). (l11, l2) \<in> set (map o1 l1) \<longleftrightarrow> (\<exists>(s1 :: 'a list). l11 = Cons x s1 \<and> (s1, l2) \<in> set l1))) \<and> (let r2 :: ('a list \<times> 'a list) list = map o1 pr in ((\<forall>(y :: 'a list \<times> 'a list). y \<in> set r2 \<longleftrightarrow> (\<exists>(x1 :: 'a list \<times> 'a list). x1 \<in> set pr \<and> y = o1 x1)) \<and> (distinct pr \<longrightarrow> injective o1 \<longrightarrow> distinct r2)) \<and> r = Cons ((Nil :: 'a list), l) r2)))) \<longrightarrow> proper_cuts r l"
  sorry
end
