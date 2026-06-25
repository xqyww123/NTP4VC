theory verifythis_2021_shearsort_modified_Top_inv_nonnegqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_NumOf" "Why3STD.int_Sum" "Why3STD.matrix_Matrix"
begin
consts fc :: "int \<Rightarrow> int matrix \<Rightarrow> int \<Rightarrow> int"
axiomatization where fc_def:   "fc x m i = int (map_occ x (elts m i) (0 :: int) (columns m))"
  for x :: "int"
  and m :: "int matrix"
  and i :: "int"
definition mocc :: "int \<Rightarrow> int matrix \<Rightarrow> int"
  where "mocc x m = sum (fc x m) (0 :: int) (rows m)" for x m
definition lt :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "lt i j k l \<longleftrightarrow> i < k \<or> i = k \<and> (if i cmod (2 :: int) = (0 :: int) then j < l else l < j)" for i j k l
definition snake_order :: "int matrix \<Rightarrow> _"
  where "snake_order m \<longleftrightarrow> (let rw :: int = rows m; cl :: int = columns m in \<forall>(i :: int) (j :: int) (k :: int) (l :: int). (0 :: int) \<le> i \<and> i < rw \<longrightarrow> (0 :: int) \<le> j \<and> j < cl \<longrightarrow> (0 :: int) \<le> k \<and> k < rw \<longrightarrow> (0 :: int) \<le> l \<and> l < cl \<longrightarrow> lt i j k l \<longrightarrow> elts m i j \<le> elts m k l)" for m
consts fc1 :: "int matrix \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool"
consts fc2 :: "int matrix \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
consts fc3 :: "int matrix \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
consts fc4 :: "int matrix \<Rightarrow> int \<Rightarrow> int"
axiomatization where fc1_def:   "fc1 m i j k l = True \<longleftrightarrow> lt i j k l \<and> elts m k l < elts m i j"
  for m :: "int matrix"
  and i :: "int"
  and j :: "int"
  and k :: "int"
  and l :: "int"
axiomatization where fc2_def:   "fc2 m i j k = numof (fc1 m i j k) (0 :: int) (columns m)"
  for m :: "int matrix"
  and i :: "int"
  and j :: "int"
  and k :: "int"
axiomatization where fc3_def:   "fc3 m i j = sum (fc2 m i j) (0 :: int) (rows m)"
  for m :: "int matrix"
  and i :: "int"
  and j :: "int"
axiomatization where fc4_def:   "fc4 m i = sum (fc3 m i) (0 :: int) (columns m)"
  for m :: "int matrix"
  and i :: "int"
definition inversions :: "int matrix \<Rightarrow> int"
  where "inversions m = sum (fc4 m) (0 :: int) (rows m)" for m
theorem inv_nonneg'vc:
  fixes m :: "int matrix"
  shows "(0 :: int) \<le> inversions m"
  sorry
end
