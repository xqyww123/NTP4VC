theory verifythis_2021_shearsort_ShearSort_numoff_occqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_NumOf" "Why3STD.int_Sum" "Why3STD.map_MapExt" "Why3STD.map_MapPermut" "Why3STD.matrix_Matrix"
begin
consts column :: "'a matrix \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'a"
axiomatization where column_def:   "column m j i = elts m i j"
  for m :: "'a matrix"
  and j :: "int"
  and i :: "int"
consts moccf :: "'a \<Rightarrow> (int \<Rightarrow> int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where moccf_def:   "moccf x e c i = int (map_occ x (e i) (0 :: int) c)"
  for x :: "'a"
  and e :: "int \<Rightarrow> int \<Rightarrow> 'a"
  and c :: "int"
  and i :: "int"
definition mocc :: "'a \<Rightarrow> (int \<Rightarrow> int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "mocc x e r c = sum (moccf x e c) (0 :: int) r" for x e r c
consts compose :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c"
axiomatization where compose_def:   "compose g f x = g (f x)"
  for g :: "'b \<Rightarrow> 'c"
  and f :: "'a \<Rightarrow> 'b"
  and x :: "'a"
theorem numoff_occ'vc:
  fixes l :: "int"
  fixes u :: "int"
  fixes p :: "'a \<Rightarrow> bool"
  fixes x :: "'a"
  fixes q :: "'a \<Rightarrow> bool"
  fixes a :: "int \<Rightarrow> 'a"
  assumes fact0: "l \<le> u"
  assumes fact1: "p x = True"
  assumes fact2: "\<forall>(y :: 'a). q y = True \<longleftrightarrow> p y = True \<and> \<not>y = x"
  shows "numof (compose p a) l u = numof (compose q a) l u + int (map_occ x a l u)"
  sorry
end
