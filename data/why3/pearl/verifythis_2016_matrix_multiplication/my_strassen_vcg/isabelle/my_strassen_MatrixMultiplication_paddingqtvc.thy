theory my_strassen_MatrixMultiplication_paddingqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_Sum" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_MyMatrix" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_MatrixArithmetic" "pearl_verifythis_2016_matrix_multiplication_lib.sum_extended_Sum_extended" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_BlockMul" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_ring_simp_Symb" "Why3STD.matrix_Matrix"
begin
definition mdl :: "'a matrix \<Rightarrow> 'a mat"
  where "mdl m = create (matrix_Matrix.rows m) (columns m) (elts m)" for m
datatype  with_symb = with_symb'mk (phy: "int matrix") (sym: "expr")
definition with_symb_vld :: "env \<Rightarrow> with_symb \<Rightarrow> _"
  where "with_symb_vld env ws \<longleftrightarrow> e_mdl env (sym ws) = mdl (phy ws) \<and> e_vld env (sym ws) \<and> e_rows (sym ws) = matrices_MyMatrix.rows (mdl (phy ws)) \<and> e_cols (sym ws) = cols (mdl (phy ws))" for env ws
theorem padding'vc:
  fixes a :: "int matrix"
  fixes r :: "int"
  fixes c :: "int"
  assumes fact0: "matrices_MyMatrix.rows (mdl a) \<le> r"
  assumes fact1: "cols (mdl a) \<le> c"
  shows "(0 :: int) \<le> r"
  and "(0 :: int) \<le> c"
  and "\<forall>(res :: int matrix). matrix_Matrix.rows res = r \<and> columns res = c \<and> (\<forall>(i :: int) (j :: int). ((0 :: int) \<le> i \<and> i < r) \<and> (0 :: int) \<le> j \<and> j < c \<longrightarrow> elts res i j = (0 :: int)) \<longrightarrow> (let nr :: int = matrix_Matrix.rows a; nc :: int = columns a in (((0 :: int) \<le> (0 :: int) \<and> (0 :: int) \<le> (0 :: int) + nr \<and> (0 :: int) + nr \<le> matrix_Matrix.rows a) \<and> ((0 :: int) \<le> (0 :: int) \<and> (0 :: int) \<le> (0 :: int) + nc \<and> (0 :: int) + nc \<le> columns a) \<and> ((0 :: int) \<le> (0 :: int) \<and> (0 :: int) \<le> (0 :: int) + nr \<and> (0 :: int) + nr \<le> matrix_Matrix.rows res) \<and> (0 :: int) \<le> (0 :: int) \<and> (0 :: int) \<le> (0 :: int) + nc \<and> (0 :: int) + nc \<le> columns res) \<and> (\<forall>(res1 :: int matrix). matrix_Matrix.rows res1 = matrix_Matrix.rows res \<and> columns res1 = columns res \<longrightarrow> (\<forall>(i :: int) (j :: int). (0 :: int) \<le> i \<and> i < (0 :: int) + nr \<longrightarrow> (0 :: int) \<le> j \<and> j < (0 :: int) + nc \<longrightarrow> elts res1 i j = elts a (i + ((0 :: int) - (0 :: int))) (j + ((0 :: int) - (0 :: int)))) \<and> (\<forall>(i :: int) (j :: int). (0 :: int) \<le> i \<and> i < matrix_Matrix.rows res1 \<longrightarrow> (0 :: int) \<le> j \<and> j < columns res1 \<longrightarrow> \<not>(((0 :: int) \<le> i \<and> i < (0 :: int) + nr) \<and> (0 :: int) \<le> j \<and> j < (0 :: int) + nc) \<longrightarrow> elts res1 i j = elts res i j) \<longrightarrow> matrices_MyMatrix.rows (mdl res1) = r \<and> cols (mdl res1) = c \<and> mdl a = block (mdl res1) (0 :: int) (matrices_MyMatrix.rows (mdl a)) (0 :: int) (cols (mdl a)) \<and> (let dr :: int = r - matrices_MyMatrix.rows (mdl a) in create dr (cols (mdl a)) zerof = block (mdl res1) (matrices_MyMatrix.rows (mdl a)) dr (0 :: int) (cols (mdl a))) \<and> (let dc :: int = c - cols (mdl a) in create (matrices_MyMatrix.rows (mdl a)) dc zerof = block (mdl res1) (0 :: int) (matrices_MyMatrix.rows (mdl a)) (cols (mdl a)) dc)))"
  sorry
end
