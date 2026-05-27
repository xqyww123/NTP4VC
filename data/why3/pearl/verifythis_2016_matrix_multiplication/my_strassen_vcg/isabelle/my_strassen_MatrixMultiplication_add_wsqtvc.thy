theory my_strassen_MatrixMultiplication_add_wsqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_Sum" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_MyMatrix" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_MatrixArithmetic" "pearl_verifythis_2016_matrix_multiplication_lib.sum_extended_Sum_extended" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_BlockMul" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_ring_simp_Symb" "Why3STD.matrix_Matrix"
begin
definition mdl :: "'a matrix \<Rightarrow> 'a mat"
  where "mdl m = create (matrix_Matrix.rows m) (columns m) (elts m)" for m
datatype  with_symb = with_symb'mk (phy: "int matrix") (sym: "expr")
definition with_symb_vld :: "env \<Rightarrow> with_symb \<Rightarrow> _"
  where "with_symb_vld env ws \<longleftrightarrow> e_mdl env (sym ws) = mdl (phy ws) \<and> e_vld env (sym ws) \<and> e_rows (sym ws) = matrices_MyMatrix.rows (mdl (phy ws)) \<and> e_cols (sym ws) = cols (mdl (phy ws))" for env ws
theorem add_ws'vc:
  fixes a :: "with_symb"
  fixes b :: "with_symb"
  fixes env :: "env"
  assumes fact0: "infix_eqeqeq (mdl (phy a)) (mdl (phy b))"
  assumes fact1: "with_symb_vld env a"
  assumes fact2: "with_symb_vld env b"
  shows "let o1 :: expr = sym b; o2 :: expr = sym a in ((e_vld env o2 \<and> e_vld env o1) \<and> e_rows o2 = e_rows o1 \<and> e_cols o2 = e_cols o1) \<and> (e_vld env (symb_add o2 o1) \<and> e_mdl env (symb_add o2 o1) = add (e_mdl env o2) (e_mdl env o1) \<longrightarrow> (let o3 :: int matrix = phy b; o4 :: int matrix = phy a in infix_eqeqeq (mdl o4) (mdl o3) \<and> (\<forall>(o5 :: int matrix). mdl o5 = add (mdl o4) (mdl o3) \<and> infix_eqeqeq (mdl o5) (mdl o4) \<longrightarrow> mdl o5 = add (mdl (phy a)) (mdl (phy b)) \<and> symb_add o2 o1 = symb_add (sym a) (sym b) \<and> with_symb_vld env (with_symb'mk o5 (symb_add o2 o1)))))"
  sorry
end
