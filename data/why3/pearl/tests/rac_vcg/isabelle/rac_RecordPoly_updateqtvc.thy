theory rac_RecordPoly_updateqtvc
  imports "NTP4Verif.NTP4Verif"
begin
datatype 'a t1 = t1'mk (x: "'a")
datatype 'a t2 = t2'mk (f: "int \<Rightarrow> 'a")
datatype 'a t3 = t3'mk (elts: "int \<Rightarrow> 'a") (length: "int")
consts o1 :: "int \<Rightarrow> 'a \<Rightarrow> (int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> 'a"
axiomatization where o1_def:   "o1 i x1 f1 j = (if j = i then x1 else f1 j)"
  for i :: "int"
  and x1 :: "'a"
  and f1 :: "int \<Rightarrow> 'a"
  and j :: "int"
theorem update'vc:
  fixes i :: "int"
  fixes r :: "'a t3"
  fixes r1 :: "'a t3"
  fixes x1 :: "'a"
  assumes fact0: "(0 :: int) < i"
  assumes fact1: "i < length r"
  assumes fact2: "\<forall>(j :: int). elts r1 j = (if j = i then x1 else elts r j)"
  assumes fact3: "length r1 = length r"
  shows "\<forall>(j :: int). (0 :: int) < j \<and> j < length r1 \<longrightarrow> \<not>j = i \<longrightarrow> elts r1 j = elts r j"
  and "elts r1 i = x1"
  sorry
end
