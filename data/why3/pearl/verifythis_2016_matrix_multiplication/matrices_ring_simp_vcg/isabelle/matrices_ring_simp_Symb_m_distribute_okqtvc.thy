theory matrices_ring_simp_Symb_m_distribute_okqtvc
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
fun lm_merge :: "mono list \<Rightarrow> mono list \<Rightarrow> mono list \<Rightarrow> mono list"
  where "lm_merge acc (Nil :: mono list) l2 = cat_rev (Nil :: mono list) (lm_collapse acc l2)" for acc l2
      | "lm_merge acc (Cons x q) l2 = (case lm_dump x acc l2 of (acc1, l21) \<Rightarrow> lm_merge (m_collapse acc1 x) q l21)" for acc x q l2
fun cat :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "cat (Nil :: 'a list) l2 = l2" for l2
      | "cat (Cons x q) l2 = Cons x (cat q l2)" for x q l2
definition m_mul :: "mono \<Rightarrow> mono \<Rightarrow> mono"
  where "m_mul m1 m2 = mono'mk (cat (m_prod m1) (m_prod m2)) (if m_pos m1 = True \<longleftrightarrow> m_pos m2 = True then True else False)" for m1 m2
fun m_distribute :: "mono \<Rightarrow> mono list \<Rightarrow> mono list"
  where "m_distribute m (Nil :: mono list) = (Nil :: mono list)" for m
      | "m_distribute m (Cons x q) = Cons (m_mul m x) (m_distribute m q)" for m x q
theorem m_distribute_ok'vc:
  fixes r :: "int"
  fixes k :: "int"
  fixes c :: "int"
  fixes f :: "int \<Rightarrow> int mat"
  fixes m :: "mono"
  fixes l :: "mono list"
  assumes fact0: "(0 :: int) \<le> r"
  assumes fact1: "(0 :: int) \<le> k"
  assumes fact2: "(0 :: int) \<le> c"
  assumes fact3: "l_vld f r k (m_prod m)"
  assumes fact4: "lm_vld f k c l"
  shows "case l of Nil \<Rightarrow> True | Cons x q \<Rightarrow> ((case l of Nil \<Rightarrow> False | Cons _ f1 \<Rightarrow> f1 = q) \<and> ((0 :: int) \<le> r \<and> (0 :: int) \<le> k \<and> (0 :: int) \<le> c) \<and> l_vld f r k (m_prod m) \<and> lm_vld f k c q) \<and> (let o1 :: mono list = m_distribute m q in lm_vld f r c o1 \<and> lm_mdl f r c o1 = mul (m_mdl f m) (lm_mdl f k c q) \<longrightarrow> ((0 :: int) \<le> r \<and> (0 :: int) \<le> k \<and> (0 :: int) \<le> c) \<and> l_vld f r k (m_prod m) \<and> l_vld f k c (m_prod x))"
  and "\<forall>(result :: mono list). (case l of Nil \<Rightarrow> result = (Nil :: mono list) | Cons x q \<Rightarrow> (let o1 :: mono list = m_distribute m q in (lm_vld f r c o1 \<and> lm_mdl f r c o1 = mul (m_mdl f m) (lm_mdl f k c q)) \<and> (let o2 :: mono = m_mul m x in (l_vld f r c (m_prod o2) \<and> m_mdl f o2 = mul (m_mdl f m) (m_mdl f x)) \<and> result = Cons o2 o1))) \<longrightarrow> (result = m_distribute m l \<and> lm_vld f r c result) \<and> lm_mdl f r c result = mul (m_mdl f m) (lm_mdl f k c l)"
  sorry
end
