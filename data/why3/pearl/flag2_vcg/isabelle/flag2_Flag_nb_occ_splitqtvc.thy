theory flag2_Flag_nb_occ_splitqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
datatype  color = Blue | White | Red
definition monochrome :: "(int \<Rightarrow> color) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> color \<Rightarrow> _"
  where "monochrome a i j c \<longleftrightarrow> (\<forall>(k :: int). i \<le> k \<and> k < j \<longrightarrow> a k = c)" for a i j c
consts nb_occ :: "(int \<Rightarrow> color) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> color \<Rightarrow> int"
axiomatization where nb_occ_def:   "if j \<le> i then nb_occ a i j c = (0 :: int) else if a (j - (1 :: int)) = c then nb_occ a i j c = (1 :: int) + nb_occ a i (j - (1 :: int)) c else nb_occ a i j c = nb_occ a i (j - (1 :: int)) c"
  for j :: "int"
  and i :: "int"
  and a :: "int \<Rightarrow> color"
  and c :: "color"
theorem nb_occ_split'vc:
  fixes i :: "int"
  fixes j :: "int"
  fixes k :: "int"
  fixes a :: "int \<Rightarrow> color"
  fixes c :: "color"
  assumes fact0: "i \<le> j"
  assumes fact1: "j \<le> k"
  shows "nb_occ a i k c = nb_occ a i j c + nb_occ a j k c"
  sorry
end
