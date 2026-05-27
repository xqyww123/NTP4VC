theory matrices_ring_simp_Symb_lm_dump_okqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_Sum" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_MyMatrix" "pearl_verifythis_2016_matrix_multiplication_lib.matrices_MatrixArithmetic" "pearl_verifythis_2016_matrix_multiplication_lib.sum_extended_Sum_extended"
begin
datatype  mono = mono'mk (m_prod: "int list") (m_pos: "bool")
fun l_mdl :: "(int \<Rightarrow> int mat) \<Rightarrow> int list \<Rightarrow> int mat"
  where "l_mdl f (Nil :: int list) = create (-(1 :: int)) (-(1 :: int)) zerof" for f
      | "l_mdl f (Cons x (Nil :: int list)) = f x" for f x
      | "l_mdl f (Cons x q) = mul (f x) (l_mdl f q)" for f x q
fun l_vld :: "(int \<Rightarrow> int mat) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> _"
  where "l_vld f r c (Nil :: int list) = False" for f r c
      | "l_vld f r c (Cons x (Nil :: int list)) = (rows (f x) = r \<and> cols (f x) = c)" for f r c x
      | "l_vld f r c (Cons x q) = (rows (f x) = r \<and> l_vld f (cols (f x)) c q)" for f r c x q
definition m_mdl :: "(int \<Rightarrow> int mat) \<Rightarrow> mono \<Rightarrow> int mat"
  where "m_mdl f m = (let m0 :: int mat = l_mdl f (m_prod m) in if m_pos m = True then m0 else opp m0)" for f m
fun lm_mdl :: "(int \<Rightarrow> int mat) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> mono list \<Rightarrow> int mat"
  where "lm_mdl f r c (Nil :: mono list) = create r c zerof" for f r c
      | "lm_mdl f r c (Cons x q) = add (lm_mdl f r c q) (m_mdl f x)" for f r c x q
fun lm_mdl_simp :: "(int \<Rightarrow> int mat) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> mono list \<Rightarrow> int mat"
  where "lm_mdl_simp f r c (Nil :: mono list) = create r c zerof" for f r c
      | "lm_mdl_simp f r c (Cons x (Nil :: mono list)) = m_mdl f x" for f r c x
      | "lm_mdl_simp f r c (Cons x q) = add (lm_mdl_simp f r c q) (m_mdl f x)" for f r c x q
fun lm_vld :: "(int \<Rightarrow> int mat) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> mono list \<Rightarrow> _"
  where "lm_vld f r c (Nil :: mono list) = True" for f r c
      | "lm_vld f r c (Cons x q) = (l_vld f r c (m_prod x) \<and> lm_vld f r c q)" for f r c x q
fun l_compare :: "int list \<Rightarrow> int list \<Rightarrow> int"
  where "l_compare (Nil :: int list) (Nil :: int list) = (0 :: int)"
      | "l_compare (Nil :: int list) x = -(1 :: int)" for x
      | "l_compare x (Nil :: int list) = (1 :: int)" for x
      | "l_compare (Cons x q) (Cons y r) = (if x < y then -(1 :: int) else if y < x then 1 :: int else l_compare q r)" for x q y r
definition m_lower :: "mono \<Rightarrow> mono \<Rightarrow> _"
  where "m_lower m1 m2 \<longleftrightarrow> (let cmp :: int = l_compare (m_prod m1) (m_prod m2) in cmp < (0 :: int) \<or> cmp = (0 :: int) \<and> (m_pos m1 = True \<longrightarrow> m_pos m2 = True))" for m1 m2
definition m_collapse :: "mono list \<Rightarrow> mono \<Rightarrow> mono list"
  where "m_collapse l m = (case l of Nil \<Rightarrow> Cons m (Nil :: mono list) | Cons x q \<Rightarrow> (if \<not>m_pos x = True \<and> m_pos m = True \<and> l_compare (m_prod m) (m_prod x) = (0 :: int) then q else Cons m l))" for l m
fun lm_collapse :: "mono list \<Rightarrow> mono list \<Rightarrow> mono list"
  where "lm_collapse acc (Nil :: mono list) = acc" for acc
      | "lm_collapse acc (Cons x q) = lm_collapse (m_collapse acc x) q" for acc x q
fun cat_rev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "cat_rev acc (Nil :: 'a list) = acc" for acc
      | "cat_rev acc (Cons x q) = cat_rev (Cons x acc) q" for acc x q
fun lm_dump :: "mono \<Rightarrow> mono list \<Rightarrow> mono list \<Rightarrow> mono list \<times> mono list"
  where "lm_dump x acc (Nil :: mono list) = (acc, (Nil :: mono list))" for x acc
      | "lm_dump x acc (Cons y q) = (if m_lower x y then (acc, Cons y q) else lm_dump x (m_collapse acc y) q)" for x acc y q
theorem lm_dump_ok'vc:
  fixes r :: "int"
  fixes c :: "int"
  fixes f :: "int \<Rightarrow> int mat"
  fixes acc :: "mono list"
  fixes l :: "mono list"
  fixes x :: "mono"
  assumes fact0: "(0 :: int) \<le> r"
  assumes fact1: "(0 :: int) \<le> c"
  assumes fact2: "lm_vld f r c acc"
  assumes fact3: "lm_vld f r c l"
  shows "case l of Nil \<Rightarrow> True | Cons y q \<Rightarrow> \<not>m_lower x y \<longrightarrow> ((lm_vld f r c acc \<and> l_vld f r c (m_prod y)) \<and> (0 :: int) \<le> r \<and> (0 :: int) \<le> c) \<and> (let o1 :: mono list = m_collapse acc y in lm_vld f r c o1 \<and> lm_mdl f r c o1 = add (lm_mdl f r c acc) (m_mdl f y) \<longrightarrow> (case l of Nil \<Rightarrow> False | Cons _ f1 \<Rightarrow> f1 = q) \<and> ((0 :: int) \<le> r \<and> (0 :: int) \<le> c) \<and> lm_vld f r c o1 \<and> lm_vld f r c q)"
  and "\<forall>(acc2 :: mono list) (l2 :: mono list). let result :: mono list \<times> mono list = (acc2, l2) in (case l of Nil \<Rightarrow> acc2 = acc \<and> l2 = (Nil :: mono list) | Cons y q \<Rightarrow> (if m_lower x y then acc2 = acc \<and> l2 = l else let o1 :: mono list = m_collapse acc y in (lm_vld f r c o1 \<and> lm_mdl f r c o1 = add (lm_mdl f r c acc) (m_mdl f y)) \<and> result = lm_dump x o1 q \<and> lm_vld f r c acc2 \<and> lm_vld f r c l2 \<and> add (lm_mdl f r c acc2) (lm_mdl f r c l2) = add (lm_mdl f r c o1) (lm_mdl f r c q))) \<longrightarrow> result = lm_dump x acc l \<and> lm_vld f r c acc2 \<and> lm_vld f r c l2 \<and> add (lm_mdl f r c acc2) (lm_mdl f r c l2) = add (lm_mdl f r c acc) (lm_mdl f r c l)"
  sorry
end
