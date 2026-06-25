theory verifythis_2021_lexicographic_permutations_2_BoxedIntArrays
  imports "NTP4Verif.NTP4Verif" "Why3STD.map_MapEq" "Why3STD.map_MapExchange" "Why3STD.map_MapPermut"
begin
definition boxed :: "int \<Rightarrow> int list \<Rightarrow> _"
  where "boxed u a \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length a) \<longrightarrow> (2 :: int) * abs (a ! nat i) < u)" for u a
consts greater :: "int list \<Rightarrow> int"
axiomatization where greater'spec'0:   "(0 :: int) \<le> greater a"
  for a :: "int list"
axiomatization where greater'spec:   "(2 :: int) * abs (a ! nat i) < greater a"
 if "(0 :: int) \<le> i"
 and "i < int (length a)"
  for i :: "int"
  and a :: "int list"
consts maxi :: "int \<Rightarrow> int list \<Rightarrow> int"
axiomatization where maxi_def:   "maxi base a = base ^\<^sub>i int (length a)"
 if "boxed base a"
  for base :: "int"
  and a :: "int list"
end
