theory coincidence_count_CoincidenceCountBag_not_mem_inter_rqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
definition increasing :: "int list \<Rightarrow> _"
  where "increasing a \<longleftrightarrow> (\<forall>(i :: int) (j :: int). (0 :: int) \<le> i \<and> i < j \<and> j < int (length a) \<longrightarrow> a ! nat i \<le> a ! nat j)" for a
consts bagofsub :: "'a list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'a multiset"
axiomatization where bagofsub_def:   "if hi \<le> lo then bagofsub a lo hi = ({#} :: 'a multiset) else bagofsub a lo hi = add_mset (a ! nat lo) (bagofsub a (lo + (1 :: int)) hi)"
 if "(0 :: int) \<le> lo"
 and "lo \<le> hi"
 and "hi \<le> int (length a)"
  for lo :: "int"
  and hi :: "int"
  and a :: "'a list"
definition bagof :: "'a list \<Rightarrow> 'a multiset"
  where "bagof a = bagofsub a (0 :: int) (int (length a))" for a
definition drop :: "'a list \<Rightarrow> int \<Rightarrow> 'a multiset"
  where "drop a i = bagofsub a i (int (length a))" for a i
theorem not_mem_inter_r'vc:
  fixes i :: "int"
  fixes a :: "int list"
  fixes s :: "int multiset"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "i < int (length a)"
  assumes fact2: "\<not>a ! nat i \<in># s"
  shows "drop a i \<inter># s = drop a (i + (1 :: int)) \<inter># s"
  sorry
end
