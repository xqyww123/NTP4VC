theory inverse_in_place_InverseInPlace_is_permutation_inverseqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_NumOf"
begin
definition prefix_tl :: "int \<Rightarrow> int"
  where "prefix_tl x = -x - (1 :: int)" for x
consts fc :: "(int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> bool"
axiomatization where fc_def:   "fc m n = True \<longleftrightarrow> (0 :: int) \<le> m n"
  for m :: "int \<Rightarrow> int"
  and n :: "int"
definition numof :: "(int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "numof m l r = int_NumOf.numof (fc m) l r" for m l r
definition is_permutation :: "int list \<Rightarrow> _"
  where "is_permutation a \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length a) \<longrightarrow> ((0 :: int) \<le> a ! nat i \<and> a ! nat i < int (length a)) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < int (length a) \<longrightarrow> \<not>i = j \<longrightarrow> \<not>a ! nat i = a ! nat j))" for a
theorem is_permutation_inverse'vc:
  fixes a :: "int list"
  fixes b :: "int list"
  assumes fact0: "length a = length b"
  assumes fact1: "is_permutation a"
  assumes fact2: "\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length b) \<longrightarrow> (0 :: int) \<le> b ! nat i \<and> b ! nat i < int (length b)"
  assumes fact3: "\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length b) \<longrightarrow> a ! nat (b ! nat i) = i"
  shows "is_permutation b"
  sorry
end
