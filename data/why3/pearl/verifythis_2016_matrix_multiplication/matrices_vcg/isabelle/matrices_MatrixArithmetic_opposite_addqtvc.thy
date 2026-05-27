theory matrices_MatrixArithmetic_opposite_addqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_Sum" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_MyMatrix" "pearl_verifythis_2016_matrix_multiplication_lib.sum_extended_Sum_extended"
begin
consts zerof :: "int \<Rightarrow> int \<Rightarrow> int"
axiomatization where zerof'def:   "zerof x x_1 = (0 :: int)"
  for x :: "int"
  and x_1 :: "int"
consts add2f :: "int mat \<Rightarrow> int mat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where add2f'def:   "add2f a b x y = get a x y + get b x y"
  for a :: "int mat"
  and b :: "int mat"
  and x :: "int"
  and y :: "int"
definition add :: "int mat \<Rightarrow> int mat \<Rightarrow> int mat"
  where "add a b = create (rows a) (cols a) (add2f a b)" for a b
consts opp2f :: "int mat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where opp2f'def:   "opp2f a x y = -get a x y"
  for a :: "int mat"
  and x :: "int"
  and y :: "int"
definition opp :: "int mat \<Rightarrow> int mat"
  where "opp a = create (rows a) (cols a) (opp2f a)" for a
definition sub :: "int mat \<Rightarrow> int mat \<Rightarrow> int mat"
  where "sub a b = add a (opp b)" for a b
consts mul_atom :: "int mat \<Rightarrow> int mat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where mul_atom'def:   "mul_atom a b i j k = get a i k * get b k j"
  for a :: "int mat"
  and b :: "int mat"
  and i :: "int"
  and j :: "int"
  and k :: "int"
consts mul_cell :: "int mat \<Rightarrow> int mat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where mul_cell'def:   "mul_cell a b i j = sum (mul_atom a b i j) (0 :: int) (cols a)"
  for a :: "int mat"
  and b :: "int mat"
  and i :: "int"
  and j :: "int"
definition mul :: "int mat \<Rightarrow> int mat \<Rightarrow> int mat"
  where "mul a b = create (rows a) (cols b) (mul_cell a b)" for a b
theorem opposite_add'vc:
  fixes m1 :: "int mat"
  fixes m2 :: "int mat"
  assumes fact0: "infix_eqeqeq m1 m2"
  shows "opp (add m1 m2) = add (opp m1) (opp m2)"
  sorry
end
