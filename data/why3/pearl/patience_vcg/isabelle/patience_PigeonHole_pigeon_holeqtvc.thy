theory patience_PigeonHole_pigeon_holeqtvc
  imports "NTP4Verif.NTP4Verif"
begin
definition range :: "(int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "range f n m \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n \<longrightarrow> (0 :: int) \<le> f i \<and> f i < m)" for f n m
definition injective :: "(int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> _"
  where "injective f n \<longleftrightarrow> (\<forall>(i :: int) (j :: int). (0 :: int) \<le> i \<and> i < j \<and> j < n \<longrightarrow> \<not>f i = f j)" for f n
consts shift :: "(int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where shift_def:   "shift f i k = (if k < i then f k else f (k + (1 :: int)))"
  for f :: "int \<Rightarrow> int"
  and i :: "int"
  and k :: "int"
theorem pigeon_hole'vc:
  fixes f :: "int \<Rightarrow> int"
  fixes n :: "int"
  fixes m :: "int"
  assumes fact0: "range f n m"
  assumes fact1: "m < n"
  assumes fact2: "(0 :: int) \<le> m"
  shows "\<not>injective f n"
  sorry
end
