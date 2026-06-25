theory strassen_MatrixTests_cut_quartersqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_Sum" "pearl_ring_decision_lib.strassen_Sum_extended" "pearl_ring_decision_lib.strassen_MaxFun" "pearl_ring_decision_lib.strassen_InfIntMatrix" "pearl_ring_decision_lib.strassen_InfIntMatrixDecision"
begin
consts cols :: "mat \<Rightarrow> int"
consts rows :: "mat \<Rightarrow> int"
axiomatization where rows_def:   "rows a = r"
 if "(0 :: int) \<le> r"
 and "(0 :: int) \<le> c"
 and "strassen_InfIntMatrix.size a r c"
  for r :: "int"
  and c :: "int"
  and a :: "mat"
axiomatization where cols_def:   "cols a = c"
 if "(0 :: int) \<le> r"
 and "(0 :: int) \<le> c"
 and "strassen_InfIntMatrix.size a r c"
  for r :: "int"
  and c :: "int"
  and a :: "mat"
definition is_finite :: "mat \<Rightarrow> _"
  where "is_finite m \<longleftrightarrow> strassen_InfIntMatrix.size m (rows m) (cols m)" for m
consts ofs2 :: "mat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where ofs2_def:   "ofs2 a ai aj i j = get a (ai + i) (aj + j)"
  for a :: "mat"
  and ai :: "int"
  and aj :: "int"
  and i :: "int"
  and j :: "int"
definition block :: "mat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> mat"
  where "block a r dr c dc = fcreate dr dc (ofs2 a r c)" for a r dr c dc
definition c_blocks :: "mat \<Rightarrow> mat \<Rightarrow> mat \<Rightarrow> _"
  where "c_blocks a a1 a2 \<longleftrightarrow> ((0 :: int) \<le> cols a1 \<and> cols a1 \<le> cols a) \<and> a1 = block a (0 :: int) (rows a) (0 :: int) (cols a1) \<and> a2 = block a (0 :: int) (rows a) (cols a1) (cols a - cols a1)" for a a1 a2
definition r_blocks :: "mat \<Rightarrow> mat \<Rightarrow> mat \<Rightarrow> _"
  where "r_blocks a a1 a2 \<longleftrightarrow> ((0 :: int) \<le> rows a1 \<and> rows a1 \<le> rows a) \<and> a1 = block a (0 :: int) (rows a1) (0 :: int) (cols a) \<and> a2 = block a (rows a1) (rows a - rows a1) (0 :: int) (cols a)" for a a1 a2
definition quarters :: "mat \<Rightarrow> mat \<Rightarrow> mat \<Rightarrow> mat \<Rightarrow> mat \<Rightarrow> _"
  where "quarters a a11 a12 a21 a22 \<longleftrightarrow> (is_finite a \<and> is_finite a11 \<and> is_finite a12 \<and> is_finite a21 \<and> is_finite a22) \<and> (rows a11 = rows a12 \<and> rows a12 = rows a21 \<and> rows a21 = rows a22 \<and> rows a22 = cols a11 \<and> cols a11 = cols a12 \<and> cols a12 = cols a21 \<and> cols a21 = cols a22) \<and> (rows a = cols a \<and> cols a = (2 :: int) * rows a11) \<and> a11 = block a (0 :: int) (rows a11) (0 :: int) (cols a11) \<and> a12 = block a (0 :: int) (rows a11) (cols a11) (cols a11) \<and> a21 = block a (rows a11) (rows a11) (0 :: int) (cols a11) \<and> a22 = block a (rows a11) (rows a11) (cols a11) (cols a11)" for a a11 a12 a21 a22
theorem cut_quarters'vc:
  fixes a :: "mat"
  assumes fact0: "is_finite a"
  assumes fact1: "rows a = cols a"
  assumes fact2: "even (rows a)"
  shows "\<not>(2 :: int) = (0 :: int)"
  and "let s :: int = rows a cdiv (2 :: int) in quarters a (block a (0 :: int) s (0 :: int) s) (block a (0 :: int) s s s) (block a s s (0 :: int) s) (block a s s s s)"
  sorry
end
