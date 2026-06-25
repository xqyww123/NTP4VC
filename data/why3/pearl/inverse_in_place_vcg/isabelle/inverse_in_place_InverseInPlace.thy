theory inverse_in_place_InverseInPlace
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
definition loopinvariant :: "int list \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "loopinvariant olda a m m' n \<longleftrightarrow> (\<forall>(e :: int). (0 :: int) \<le> e \<and> e < n \<longrightarrow> -n \<le> a ! nat e \<and> a ! nat e < n) \<and> (\<forall>(e :: int). m < e \<and> e < n \<longrightarrow> (0 :: int) \<le> a ! nat e) \<and> (\<forall>(e :: int). m < e \<and> e < n \<longrightarrow> olda ! nat (a ! nat e) = e) \<and> (\<forall>(e :: int). (0 :: int) \<le> e \<and> e \<le> m' \<longrightarrow> (0 :: int) \<le> a ! nat e \<longrightarrow> olda ! nat e = a ! nat e) \<and> (\<forall>(e :: int). (0 :: int) \<le> e \<and> e \<le> m \<longrightarrow> a ! nat e \<le> m) \<and> (\<forall>(e :: int). (0 :: int) \<le> e \<and> e \<le> m' \<longrightarrow> a ! nat e < (0 :: int) \<longrightarrow> olda ! nat (prefix_tl (a ! nat e)) = e \<and> (prefix_tl (a ! nat e) \<le> m \<longrightarrow> a ! nat (prefix_tl (a ! nat e)) < (0 :: int)))" for olda a m m' n
end
