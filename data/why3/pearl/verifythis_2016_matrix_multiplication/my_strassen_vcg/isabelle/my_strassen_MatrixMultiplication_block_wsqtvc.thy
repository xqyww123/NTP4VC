theory my_strassen_MatrixMultiplication_block_wsqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_Sum" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_MyMatrix" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_MatrixArithmetic" "pearl_verifythis_2016_matrix_multiplication_lib.sum_extended_Sum_extended" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_BlockMul" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_ring_simp_Symb" "Why3STD.matrix_Matrix"
begin
definition mdl :: "'a matrix \<Rightarrow> 'a mat"
  where "mdl m = create (matrix_Matrix.rows m) (columns m) (elts m)" for m
datatype  with_symb = with_symb'mk (phy: "int matrix") (sym: "expr")
definition with_symb_vld :: "env \<Rightarrow> with_symb \<Rightarrow> _"
  where "with_symb_vld env ws \<longleftrightarrow> e_mdl env (sym ws) = mdl (phy ws) \<and> e_vld env (sym ws) \<and> e_rows (sym ws) = matrices_MyMatrix.rows (mdl (phy ws)) \<and> e_cols (sym ws) = cols (mdl (phy ws))" for env ws
theorem block_ws'vc:
  fixes r :: "int"
  fixes dr :: "int"
  fixes a :: "int matrix"
  fixes c :: "int"
  fixes dc :: "int"
  fixes env1 :: "env"
  assumes fact0: "(0 :: int) \<le> r"
  assumes fact1: "r \<le> r + dr"
  assumes fact2: "r + dr \<le> matrices_MyMatrix.rows (mdl a)"
  assumes fact3: "(0 :: int) \<le> c"
  assumes fact4: "c \<le> c + dc"
  assumes fact5: "c + dc \<le> cols (mdl a)"
  shows "(0 :: int) \<le> r"
  and "r \<le> r + dr"
  and "r + dr \<le> matrices_MyMatrix.rows (mdl a)"
  and "(0 :: int) \<le> c"
  and "c \<le> c + dc"
  and "c + dc \<le> cols (mdl a)"
  and "\<forall>(m :: int matrix). mdl m = block (mdl a) r dr c dc \<and> matrices_MyMatrix.rows (mdl m) = dr \<and> cols (mdl m) = dc \<longrightarrow> (let o1 :: int mat = mdl m in \<forall>(env :: env). ev_c env = ev_c env1 + (1 :: int) \<and> ev_f env = extends1 (ev_f env1) (ev_c env1) o1 \<and> e_vld env (symb_mat o1 (ev_c env1)) \<longrightarrow> (let rm :: int mat = mdl m in rm = block (mdl a) r dr c dc \<and> matrices_MyMatrix.rows rm = dr \<and> cols rm = dc) \<and> symb_mat o1 (ev_c env1) = symb_mat (mdl m) (ev_c env1) \<and> ev_f env = extends1 (ev_f env1) (ev_c env1) (mdl m) \<and> ev_c env = ev_c env1 + (1 :: int) \<and> with_symb_vld env (with_symb'mk m (symb_mat o1 (ev_c env1))))"
  sorry
end
