theory optimal_replay_OptimalReplay
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
consts n :: "int"
axiomatization where n_def:   "(0 :: int) < n"
consts f :: "int \<Rightarrow> int"
axiomatization where f'spec'0:   "(0 :: int) \<le> f k"
 if "(0 :: int) < k"
 and "k < n"
  for k :: "int"
axiomatization where f'spec'1:   "f k < k"
 if "(0 :: int) < k"
 and "k < n"
  for k :: "int"
inductive path :: "int \<Rightarrow> int \<Rightarrow> bool" where
   path0: "path (0 :: int) (0 :: int)"
 | paths: "(0 :: int) \<le> i \<Longrightarrow> i < n \<Longrightarrow> path d j \<Longrightarrow> f i \<le> j \<Longrightarrow> j < i \<Longrightarrow> path (d + (1 :: int)) i" for i :: "int" and d :: "int" and j :: "int"
definition distance :: "int \<Rightarrow> int \<Rightarrow> _"
  where "distance d i \<longleftrightarrow> path d i \<and> (\<forall>(d' :: int). path d' i \<longrightarrow> d \<le> d')" for d i
end
