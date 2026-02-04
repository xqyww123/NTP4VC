theory naive_MatrixMultiplication
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_Sum" "Why3STD.matrix_Matrix"
begin
consts mul_atom :: "int matrix \<Rightarrow> int matrix \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where mul_atom'def:   "mul_atom a b i j k = elts a i k * elts b k j"
  for a :: "int matrix"
  and b :: "int matrix"
  and i :: "int"
  and j :: "int"
  and k :: "int"
definition matrix_product :: "int matrix \<Rightarrow> int matrix \<Rightarrow> int matrix \<Rightarrow> _"
  where "matrix_product m a b \<longleftrightarrow> (\<forall>(i :: int) (j :: int). (0 :: int) \<le> i \<and> i < rows m \<longrightarrow> (0 :: int) \<le> j \<and> j < columns m \<longrightarrow> elts m i j = sum (mul_atom a b i j) (0 :: int) (columns a))" for m a b
end
