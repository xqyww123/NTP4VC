theory verifythis_2019_cartesian_trees_Top_find_smallerqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.exn_Exn"
begin
axiomatization where Trans:   "z \<le> x"
 if "y \<le> x"
 and "z \<le> y"
  for y :: "int"
  and x :: "int"
  and z :: "int"
inductive sorted :: "int list \<Rightarrow> bool" where
   Sorted_Nil: "sorted (Nil :: int list)"
 | Sorted_One: "sorted (Cons x (Nil :: int list))" for x :: "int"
 | Sorted_Two: "y \<le> x \<Longrightarrow> sorted (Cons y l) \<Longrightarrow> sorted (Cons x (Cons y l))" for y :: "int" and x :: "int" and l :: "int list"
axiomatization where sorted_mem:   "(\<forall>(y :: int). y \<in> set l \<longrightarrow> y \<le> x) \<and> sorted l \<longleftrightarrow> sorted (Cons x l)"
  for l :: "int list"
  and x :: "int"
axiomatization where sorted_append:   "sorted l1 \<and> sorted l2 \<and> (\<forall>(x :: int) (y :: int). x \<in> set l1 \<longrightarrow> y \<in> set l2 \<longrightarrow> y \<le> x) \<longleftrightarrow> sorted (l1 @ l2)"
  for l1 :: "int list"
  and l2 :: "int list"
consts destruct :: "'xi list \<Rightarrow> 'xi \<times> 'xi list"
axiomatization where destruct_def:   "case l of Cons h t \<Rightarrow> destruct l = (h, t) | _ \<Rightarrow> False"
 if "\<not>is_Nil l"
  for l :: "'xi list"
consts peek :: "'xi list \<Rightarrow> 'xi"
axiomatization where peek_def:   "case destruct l of (h, _) \<Rightarrow> peek l = h"
 if "\<not>is_Nil l"
  for l :: "'xi list"
axiomatization where peek'spec:   "peek l \<in> set l"
 if "\<not>is_Nil l"
  for l :: "'xi list"
consts tail :: "'xi list \<Rightarrow> 'xi list"
axiomatization where tail_def:   "case destruct l of (_, t) \<Rightarrow> tail l = t"
 if "\<not>is_Nil l"
  for l :: "'xi list"
datatype  dir = dir'mk (left1: "int option") (right1: "int option")
typedecl  dirs
definition parent :: "dir list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "parent t p s \<longleftrightarrow> left1 (t ! nat p) = Some s \<or> right1 (t ! nat p) = Some s" for t p s
inductive descendant :: "dir list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
   Self: "p = s \<Longrightarrow> descendant t p s" for p :: "int" and s :: "int" and t :: "dir list"
 | Son_left: "descendant t p s1 \<Longrightarrow> left1 (t ! nat s1) = Some s2 \<Longrightarrow> descendant t p s2" for t :: "dir list" and p :: "int" and s1 :: "int" and s2 :: "int"
 | Son_right: "descendant t p s1 \<Longrightarrow> right1 (t ! nat s1) = Some s2 \<Longrightarrow> descendant t p s2" for t :: "dir list" and p :: "int" and s1 :: "int" and s2 :: "int"
definition is_smallest :: "int list \<Rightarrow> int \<Rightarrow> _"
  where "is_smallest a i \<longleftrightarrow> ((0 :: int) \<le> i \<and> i < int (length a)) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < int (length a) \<longrightarrow> a ! nat i \<le> a ! nat j)" for a i
theorem find_smaller'vc:
  fixes a :: "int list"
  shows "let o1 :: int = int (length a) - (1 :: int) in ((0 :: int) \<le> o1 + (1 :: int) \<longrightarrow> (\<forall>(m :: int option). (\<forall>(i :: int). ((0 :: int) \<le> i \<and> i \<le> o1) \<and> (case m of Some mv \<Rightarrow> ((0 :: int) \<le> mv \<and> mv < int (length a)) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < i \<longrightarrow> a ! nat mv \<le> a ! nat j) | None \<Rightarrow> i = (0 :: int)) \<longrightarrow> (case m of Some mv \<Rightarrow> ((0 :: int) \<le> i \<and> i < int (length a)) \<and> ((0 :: int) \<le> mv \<and> mv < int (length a)) \<and> (if a ! nat i < a ! nat mv then case Some i of Some mv1 \<Rightarrow> ((0 :: int) \<le> mv1 \<and> mv1 < int (length a)) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < i + (1 :: int) \<longrightarrow> a ! nat mv1 \<le> a ! nat j) | None \<Rightarrow> i + (1 :: int) = (0 :: int) else (case m of Some mv1 \<Rightarrow> ((0 :: int) \<le> mv1 \<and> mv1 < int (length a)) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < i + (1 :: int) \<longrightarrow> a ! nat mv1 \<le> a ! nat j) | None \<Rightarrow> i + (1 :: int) = (0 :: int))) | _ \<Rightarrow> (case Some i of Some mv \<Rightarrow> ((0 :: int) \<le> mv \<and> mv < int (length a)) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < i + (1 :: int) \<longrightarrow> a ! nat mv \<le> a ! nat j) | None \<Rightarrow> i + (1 :: int) = (0 :: int)))) \<and> ((case m of Some mv \<Rightarrow> ((0 :: int) \<le> mv \<and> mv < int (length a)) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < o1 + (1 :: int) \<longrightarrow> a ! nat mv \<le> a ! nat j) | None \<Rightarrow> o1 + (1 :: int) = (0 :: int)) \<longrightarrow> (case m of Some mv \<Rightarrow> is_smallest a mv | None \<Rightarrow> int (length a) = (0 :: int))))) \<and> (o1 + (1 :: int) < (0 :: int) \<longrightarrow> int (length a) = (0 :: int))"
  sorry
end
