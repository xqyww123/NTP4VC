theory my_strassen_MatrixMultiplication_blockqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_Sum" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_MyMatrix" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_MatrixArithmetic" "pearl_verifythis_2016_matrix_multiplication_lib.sum_extended_Sum_extended" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_BlockMul" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_ring_simp_Symb" "Why3STD.matrix_Matrix"
begin
definition mdl :: "'a matrix \<Rightarrow> 'a mat"
  where "mdl m = create (matrix_Matrix.rows m) (columns m) (elts m)" for m
datatype  with_symb = with_symb'mk (phy: "int matrix") (sym: "expr")
definition with_symb_vld :: "env \<Rightarrow> with_symb \<Rightarrow> _"
  where "with_symb_vld env ws \<longleftrightarrow> e_mdl env (sym ws) = mdl (phy ws) \<and> e_vld env (sym ws) \<and> e_rows (sym ws) = matrices_MyMatrix.rows (mdl (phy ws)) \<and> e_cols (sym ws) = cols (mdl (phy ws))" for env ws
theorem block'vc:
  fixes r :: "int"
  fixes dr :: "int"
  fixes a :: "int matrix"
  fixes c :: "int"
  fixes dc :: "int"
  assumes fact0: "(0 :: int) \<le> r"
  assumes fact1: "r \<le> r + dr"
  assumes fact2: "r + dr \<le> matrices_MyMatrix.rows (mdl a)"
  assumes fact3: "(0 :: int) \<le> c"
  assumes fact4: "c \<le> c + dc"
  assumes fact5: "c + dc \<le> cols (mdl a)"
  shows "(0 :: int) \<le> dr"
  and "(0 :: int) \<le> dc"
  and "\<forall>(res :: int matrix). matrix_Matrix.rows res = dr \<and> columns res = dc \<and> (\<forall>(i :: int) (j :: int). ((0 :: int) \<le> i \<and> i < dr) \<and> (0 :: int) \<le> j \<and> j < dc \<longrightarrow> elts res i j = (0 :: int)) \<longrightarrow> (((0 :: int) \<le> r \<and> r \<le> r + dr \<and> r + dr \<le> matrix_Matrix.rows a) \<and> ((0 :: int) \<le> c \<and> c \<le> c + dc \<and> c + dc \<le> columns a) \<and> ((0 :: int) \<le> (0 :: int) \<and> (0 :: int) \<le> (0 :: int) + dr \<and> (0 :: int) + dr \<le> matrix_Matrix.rows res) \<and> (0 :: int) \<le> (0 :: int) \<and> (0 :: int) \<le> (0 :: int) + dc \<and> (0 :: int) + dc \<le> columns res) \<and> (\<forall>(res1 :: int matrix). matrix_Matrix.rows res1 = matrix_Matrix.rows res \<and> columns res1 = columns res \<longrightarrow> (\<forall>(i :: int) (j :: int). (0 :: int) \<le> i \<and> i < (0 :: int) + dr \<longrightarrow> (0 :: int) \<le> j \<and> j < (0 :: int) + dc \<longrightarrow> elts res1 i j = elts a (i + (r - (0 :: int))) (j + (c - (0 :: int)))) \<and> (\<forall>(i :: int) (j :: int). (0 :: int) \<le> i \<and> i < matrix_Matrix.rows res1 \<longrightarrow> (0 :: int) \<le> j \<and> j < columns res1 \<longrightarrow> \<not>(((0 :: int) \<le> i \<and> i < (0 :: int) + dr) \<and> (0 :: int) \<le> j \<and> j < (0 :: int) + dc) \<longrightarrow> elts res1 i j = elts res i j) \<longrightarrow> mdl res1 = block (mdl a) r dr c dc \<and> matrices_MyMatrix.rows (mdl res1) = dr \<and> cols (mdl res1) = dc)"
  sorry
end
