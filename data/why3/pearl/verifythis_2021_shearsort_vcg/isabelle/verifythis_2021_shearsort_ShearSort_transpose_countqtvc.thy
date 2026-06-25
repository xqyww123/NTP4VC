theory verifythis_2021_shearsort_ShearSort_transpose_countqtvc
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
theorem transpose_count'vc:
  fixes r :: "int"
  fixes c :: "int"
  fixes e1 :: "int \<Rightarrow> int \<Rightarrow> 'a"
  fixes e2 :: "int \<Rightarrow> int \<Rightarrow> 'a"
  fixes x :: "'a"
  assumes fact0: "(0 :: int) \<le> r"
  assumes fact1: "(0 :: int) \<le> c"
  assumes fact2: "\<forall>(i :: int) (j :: int). ((0 :: int) \<le> i \<and> i < r) \<and> (0 :: int) \<le> j \<and> j < c \<longrightarrow> e1 i j = e2 j i"
  shows "mocc x e1 r c = mocc x e2 c r"
  sorry
end
