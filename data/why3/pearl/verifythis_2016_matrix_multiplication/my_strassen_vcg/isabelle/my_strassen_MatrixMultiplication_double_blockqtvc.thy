theory my_strassen_MatrixMultiplication_double_blockqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_Sum" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_MyMatrix" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_MatrixArithmetic" "pearl_verifythis_2016_matrix_multiplication_lib.sum_extended_Sum_extended" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_BlockMul" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_ring_simp_Symb" "Why3STD.matrix_Matrix"
begin
definition mdl :: "'a matrix \<Rightarrow> 'a mat"
  where "mdl m = create (matrix_Matrix.rows m) (columns m) (elts m)" for m
datatype  with_symb = with_symb'mk (phy: "int matrix") (sym: "expr")
definition with_symb_vld :: "env \<Rightarrow> with_symb \<Rightarrow> _"
  where "with_symb_vld env ws \<longleftrightarrow> e_mdl env (sym ws) = mdl (phy ws) \<and> e_vld env (sym ws) \<and> e_rows (sym ws) = matrices_MyMatrix.rows (mdl (phy ws)) \<and> e_cols (sym ws) = cols (mdl (phy ws))" for env ws
theorem double_block'vc:
  fixes r1 :: "int"
  fixes dr1 :: "int"
  fixes a :: "int matrix"
  fixes c1 :: "int"
  fixes dc1 :: "int"
  fixes r2 :: "int"
  fixes dr2 :: "int"
  fixes c2 :: "int"
  fixes dc2 :: "int"
  assumes fact0: "(0 :: int) \<le> r1"
  assumes fact1: "r1 \<le> r1 + dr1"
  assumes fact2: "r1 + dr1 \<le> matrices_MyMatrix.rows (mdl a)"
  assumes fact3: "(0 :: int) \<le> c1"
  assumes fact4: "c1 \<le> c1 + dc1"
  assumes fact5: "c1 + dc1 \<le> cols (mdl a)"
  assumes fact6: "(0 :: int) \<le> r2"
  assumes fact7: "r2 \<le> r2 + dr2"
  assumes fact8: "r2 + dr2 \<le> dr1"
  assumes fact9: "(0 :: int) \<le> c2"
  assumes fact10: "c2 \<le> c2 + dc2"
  assumes fact11: "c2 + dc2 \<le> dc1"
  shows "block (block (mdl a) r1 dr1 c1 dc1) r2 dr2 c2 dc2 = block (mdl a) (r1 + r2) dr2 (c1 + c2) dc2"
  sorry
end
