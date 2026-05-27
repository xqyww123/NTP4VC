theory my_strassen_MatrixMultiplication_mul_naiveqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_Sum" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_MyMatrix" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_MatrixArithmetic" "pearl_verifythis_2016_matrix_multiplication_lib.sum_extended_Sum_extended" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_BlockMul" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_ring_simp_Symb" "Why3STD.matrix_Matrix"
begin
definition mdl :: "'a matrix \<Rightarrow> 'a mat"
  where "mdl m = create (matrix_Matrix.rows m) (columns m) (elts m)" for m
datatype  with_symb = with_symb'mk (phy: "int matrix") (sym: "expr")
definition with_symb_vld :: "env \<Rightarrow> with_symb \<Rightarrow> _"
  where "with_symb_vld env ws \<longleftrightarrow> e_mdl env (sym ws) = mdl (phy ws) \<and> e_vld env (sym ws) \<and> e_rows (sym ws) = matrices_MyMatrix.rows (mdl (phy ws)) \<and> e_cols (sym ws) = cols (mdl (phy ws))" for env ws
theorem mul_naive'vc:
  shows "True"
  sorry
end
