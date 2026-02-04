theory matrices_BlockMul
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_Sum" "../../lib/isabelle/matrices_MyMatrix" "../../lib/isabelle/matrices_MatrixArithmetic" "../../lib/isabelle/sum_extended_Sum_extended"
begin
consts ofs2 :: "int mat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where ofs2'def:   "ofs2 a ai aj i j = get a (ai + i) (aj + j)"
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
end
