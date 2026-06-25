theory anagrammi_Top_anagrammiqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
typedecl  line
definition perm4 :: "int list \<Rightarrow> _"
  where "perm4 s \<longleftrightarrow> int (length s) = (4 :: int) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < (4 :: int) \<longrightarrow> (1 :: int) \<le> s ! nat i \<and> s ! nat i \<le> (4 :: int)) \<and> distinct s" for s
definition lt :: "int list \<Rightarrow> int list \<Rightarrow> _"
  where "lt s1 s2 \<longleftrightarrow> (\<exists>(i :: int). ((0 :: int) \<le> i \<and> i < (4 :: int)) \<and> s1 ! nat i < s2 ! nat i \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < i \<longrightarrow> s1 ! nat j = s2 ! nat j))" for s1 s2
definition sorted :: "int list list \<Rightarrow> _"
  where "sorted o1 \<longleftrightarrow> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < int (length o1) \<longrightarrow> perm4 (o1 ! nat j)) \<and> (\<forall>(j1 :: int) (j2 :: int). (0 :: int) \<le> j1 \<and> j1 < j2 \<and> j2 < int (length o1) \<longrightarrow> lt (o1 ! nat j1) (o1 ! nat j2))" for o1
definition below :: "int list list \<Rightarrow> (int list \<Rightarrow> bool) \<Rightarrow> _"
  where "below o1 pr \<longleftrightarrow> sorted o1 \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < int (length o1) \<longrightarrow> pr (o1 ! nat j) = True) \<and> (\<forall>(s :: int list). perm4 s \<longrightarrow> pr s = True \<longrightarrow> s \<in> set o1)" for o1 pr
consts pr1 :: "int \<Rightarrow> int list \<Rightarrow> bool"
axiomatization where pr1_def:   "pr1 i1 s = True \<longleftrightarrow> s ! (0 :: nat) < i1"
  for i1 :: "int"
  and s :: "int list"
consts pr2 :: "int \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> bool"
axiomatization where pr2_def:   "pr2 i1 i2 s = True \<longleftrightarrow> pr1 i1 s = True \<or> s ! (0 :: nat) = i1 \<and> s ! (1 :: nat) < i2"
  for i1 :: "int"
  and i2 :: "int"
  and s :: "int list"
consts pr3 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> bool"
axiomatization where pr3_def:   "pr3 i1 i2 i3 s = True \<longleftrightarrow> pr2 i1 i2 s = True \<or> s ! (0 :: nat) = i1 \<and> s ! (1 :: nat) = i2 \<and> s ! (2 :: nat) < i3"
  for i1 :: "int"
  and i2 :: "int"
  and i3 :: "int"
  and s :: "int list"
consts fc :: "int list \<Rightarrow> bool"
consts fc1 :: "int list \<Rightarrow> bool"
axiomatization where fc_def:   "fc x = True"
  for x :: "int list"
axiomatization where fc1_def:   "fc1 x = True"
  for x :: "int list"
theorem anagrammi'vc:
  shows "(1 :: int) \<le> (4 :: int) + (1 :: int) \<longrightarrow> below [] (pr1 (1 :: int)) \<and> (\<forall>(output :: int list list). (\<forall>(i1 :: int). ((1 :: int) \<le> i1 \<and> i1 \<le> (4 :: int)) \<and> below output (pr1 i1) \<longrightarrow> ((1 :: int) \<le> (4 :: int) + (1 :: int) \<longrightarrow> below output (pr2 i1 (1 :: int)) \<and> (\<forall>(output1 :: int list list). (\<forall>(i2 :: int). ((1 :: int) \<le> i2 \<and> i2 \<le> (4 :: int)) \<and> below output1 (pr2 i1 i2) \<longrightarrow> (if i2 = i1 then below output1 (pr2 i1 (i2 + (1 :: int))) else ((1 :: int) \<le> (4 :: int) + (1 :: int) \<longrightarrow> below output1 (pr3 i1 i2 (1 :: int)) \<and> (\<forall>(output2 :: int list list). (\<forall>(i3 :: int). ((1 :: int) \<le> i3 \<and> i3 \<le> (4 :: int)) \<and> below output2 (pr3 i1 i2 i3) \<longrightarrow> (if i3 = i1 then below output2 (pr3 i1 i2 (i3 + (1 :: int))) else if i3 = i2 then below output2 (pr3 i1 i2 (i3 + (1 :: int))) else let i4 :: int = (10 :: int) - (i1 + i2 + i3); o1 :: int list = []; o2 :: int list = Cons i4 o1 in int (length o2) = (1 :: int) + int (length o1) \<and> o2 ! (0 :: nat) = i4 \<and> (\<forall>(i :: int). (0 :: int) < i \<and> i \<le> int (length o1) \<longrightarrow> o2 ! nat i = o1 ! nat (i - (1 :: int))) \<longrightarrow> (let o3 :: int list = Cons i3 o2 in int (length o3) = (1 :: int) + int (length o2) \<and> o3 ! (0 :: nat) = i3 \<and> (\<forall>(i :: int). (0 :: int) < i \<and> i \<le> int (length o2) \<longrightarrow> o3 ! nat i = o2 ! nat (i - (1 :: int))) \<longrightarrow> (let o4 :: int list = Cons i2 o3 in int (length o4) = (1 :: int) + int (length o3) \<and> o4 ! (0 :: nat) = i2 \<and> (\<forall>(i :: int). (0 :: int) < i \<and> i \<le> int (length o3) \<longrightarrow> o4 ! nat i = o3 ! nat (i - (1 :: int))) \<longrightarrow> (let line1 :: int list = Cons i1 o4 in int (length line1) = (1 :: int) + int (length o4) \<and> line1 ! (0 :: nat) = i1 \<and> (\<forall>(i :: int). (0 :: int) < i \<and> i \<le> int (length o4) \<longrightarrow> line1 ! nat i = o4 ! nat (i - (1 :: int))) \<longrightarrow> (let o5 :: int list list = output2 @ [line1] in int (length o5) = (1 :: int) + int (length output2) \<and> o5 ! length output2 = line1 \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length output2) \<longrightarrow> o5 ! nat i = output2 ! nat i) \<longrightarrow> below o5 (pr3 i1 i2 (i3 + (1 :: int))))))))) \<and> (below output2 (pr3 i1 i2 ((4 :: int) + (1 :: int))) \<longrightarrow> below output2 (pr2 i1 (i2 + (1 :: int)))))) \<and> ((4 :: int) + (1 :: int) < (1 :: int) \<longrightarrow> below output1 (pr2 i1 (i2 + (1 :: int)))))) \<and> (below output1 (pr2 i1 ((4 :: int) + (1 :: int))) \<longrightarrow> below output1 (pr1 (i1 + (1 :: int)))))) \<and> ((4 :: int) + (1 :: int) < (1 :: int) \<longrightarrow> below output (pr1 (i1 + (1 :: int))))) \<and> (below output (pr1 ((4 :: int) + (1 :: int))) \<longrightarrow> below output fc))"
  and "(4 :: int) + (1 :: int) < (1 :: int) \<longrightarrow> below [] fc1"
  sorry
end
