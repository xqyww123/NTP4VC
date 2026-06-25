theory verifythis_2021_shearsort_ShearSortComplete_sortqtrefnqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_NumOf" "Why3STD.int_Sum" "Why3STD.map_MapExt" "Why3STD.map_MapEq" "Why3STD.map_MapExchange" "Why3STD.map_MapPermut" "Why3STD.array_IntArraySorted" "Why3STD.matrix_Matrix" "./verifythis_2021_shearsort_Quicksort"
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
theorem sort'refn'vc:
  fixes a :: "int list"
  fixes a1 :: "int list"
  assumes fact0: "length a = length a1"
  assumes fact1: "array_IntArraySorted.sorted a"
  assumes fact2: "a1 <~~> a"
  shows "\<forall>(i :: int) (j :: int). (0 :: int) \<le> i \<and> i \<le> j \<and> j < int (length a) \<longrightarrow> a ! nat i \<le> a ! nat j"
  and "permut (nth a o nat) (nth a1 o nat) (0 :: int) (int (length a))"
  sorry
end
