theory matrices_BlockMul_mul_block_cellqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_Sum" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_MyMatrix" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_MatrixArithmetic" "pearl_verifythis_2016_matrix_multiplication_lib.sum_extended_Sum_extended"
begin
consts ofs2 :: "int mat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where ofs2_def:   "ofs2 a ai aj i j = get a (ai + i) (aj + j)"
  for a :: "int mat"
  and ai :: "int"
  and aj :: "int"
  and i :: "int"
  and j :: "int"
definition block :: "int mat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int mat"
  where "block a r dr c dc = create dr dc (ofs2 a r c)" for a r dr c dc
definition c_blocks :: "int mat \<Rightarrow> int mat \<Rightarrow> int mat \<Rightarrow> _"
  where "c_blocks a a1 a2 \<longleftrightarrow> ((0 :: int) \<le> cols a1 \<and> cols a1 \<le> cols a) \<and> a1 = block a (0 :: int) (rows a) (0 :: int) (cols a1) \<and> a2 = block a (0 :: int) (rows a) (cols a1) (cols a - cols a1)" for a a1 a2
definition r_blocks :: "int mat \<Rightarrow> int mat \<Rightarrow> int mat \<Rightarrow> _"
  where "r_blocks a a1 a2 \<longleftrightarrow> ((0 :: int) \<le> rows a1 \<and> rows a1 \<le> rows a) \<and> a1 = block a (0 :: int) (rows a1) (0 :: int) (cols a) \<and> a2 = block a (rows a1) (rows a - rows a1) (0 :: int) (cols a)" for a a1 a2
theorem mul_block_cell'vc:
  fixes a :: "int mat"
  fixes b :: "int mat"
  fixes r :: "int"
  fixes dr :: "int"
  fixes c :: "int"
  fixes dc :: "int"
  fixes i :: "int"
  fixes j :: "int"
  assumes fact0: "cols a = rows b"
  assumes fact1: "(0 :: int) \<le> r"
  assumes fact2: "r + dr \<le> rows a"
  assumes fact3: "(0 :: int) \<le> c"
  assumes fact4: "c + dc \<le> cols b"
  assumes fact5: "(0 :: int) \<le> i"
  assumes fact6: "i < dr"
  assumes fact7: "(0 :: int) \<le> j"
  assumes fact8: "j < dc"
  shows "ofs2 (mul a b) r c i j = get (mul (block a r dr (0 :: int) (cols a)) (block b (0 :: int) (rows b) c dc)) i j"
  sorry
end
