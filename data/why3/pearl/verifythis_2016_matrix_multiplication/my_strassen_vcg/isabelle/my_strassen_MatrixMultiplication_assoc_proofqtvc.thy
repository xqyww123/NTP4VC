theory my_strassen_MatrixMultiplication_assoc_proofqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_Sum" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_MyMatrix" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_MatrixArithmetic" "pearl_verifythis_2016_matrix_multiplication_lib.sum_extended_Sum_extended" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_BlockMul" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_ring_simp_Symb" "Why3STD.matrix_Matrix"
begin
definition mdl :: "'a matrix \<Rightarrow> 'a mat"
  where "mdl m = create (matrix_Matrix.rows m) (columns m) (elts m)" for m
datatype  with_symb = with_symb'mk (phy: "int matrix") (sym: "expr")
definition with_symb_vld :: "env \<Rightarrow> with_symb \<Rightarrow> _"
  where "with_symb_vld env ws \<longleftrightarrow> e_mdl env (sym ws) = mdl (phy ws) \<and> e_vld env (sym ws) \<and> e_rows (sym ws) = matrices_MyMatrix.rows (mdl (phy ws)) \<and> e_cols (sym ws) = cols (mdl (phy ws))" for env ws
theorem assoc_proof'vc:
  fixes a :: "int matrix"
  fixes b :: "int matrix"
  fixes c :: "int matrix"
  assumes fact0: "cols (mdl a) = matrices_MyMatrix.rows (mdl b)"
  assumes fact1: "cols (mdl b) = matrices_MyMatrix.rows (mdl c)"
  shows "cols (mdl a) = matrices_MyMatrix.rows (mdl b)"
  and "\<forall>(ab :: int matrix). matrices_MyMatrix.rows (mdl ab) = matrices_MyMatrix.rows (mdl a) \<and> cols (mdl ab) = cols (mdl b) \<and> mdl ab = mul (mdl a) (mdl b) \<longrightarrow> cols (mdl b) = matrices_MyMatrix.rows (mdl c) \<and> (\<forall>(bc :: int matrix). matrices_MyMatrix.rows (mdl bc) = matrices_MyMatrix.rows (mdl b) \<and> cols (mdl bc) = cols (mdl c) \<and> mdl bc = mul (mdl b) (mdl c) \<longrightarrow> cols (mdl ab) = matrices_MyMatrix.rows (mdl c) \<and> (\<forall>(ab_c :: int matrix). matrices_MyMatrix.rows (mdl ab_c) = matrices_MyMatrix.rows (mdl ab) \<and> cols (mdl ab_c) = cols (mdl c) \<and> mdl ab_c = mul (mdl ab) (mdl c) \<longrightarrow> cols (mdl a) = matrices_MyMatrix.rows (mdl bc)))"
  sorry
end
