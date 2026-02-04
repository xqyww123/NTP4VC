theory matrices_ring_simp_Symb
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_Sum" "../../lib/isabelle/matrices_MyMatrix" "../../lib/isabelle/matrices_MatrixArithmetic" "../../lib/isabelle/sum_extended_Sum_extended"
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
fun lm_distribute :: "mono list \<Rightarrow> mono list \<Rightarrow> mono list"
  where "lm_distribute (Nil :: mono list) l2 = (Nil :: mono list)" for l2
      | "lm_distribute (Cons x q) l2 = lm_merge (Nil :: mono list) (m_distribute x l2) (lm_distribute q l2)" for x q l2
fun lm_opp :: "mono list \<Rightarrow> mono list"
  where "lm_opp (Nil :: mono list) = (Nil :: mono list)"
      | "lm_opp (Cons x q) = lm_merge (Nil :: mono list) (Cons (mono'mk (m_prod x) (if \<not>m_pos x = True then True else False)) (Nil :: mono list)) (lm_opp q)" for x q
consts fc :: "int \<Rightarrow> int \<Rightarrow> int mat"
axiomatization where fc'def:   "fc y0 y1 = create y0 y1 zerof"
  for y0 :: "int"
  and y1 :: "int"
definition empty :: "int \<Rightarrow> int mat"
  where "empty = fc (0 :: int)"
datatype  env = env'mk (ev_f: "int \<Rightarrow> int mat") (ev_c: "int")
datatype  expr = expr'mk (e_body: "mono list") (e_rows: "int") (e_cols: "int")
definition e_vld :: "env \<Rightarrow> expr \<Rightarrow> _"
  where "e_vld env1 e \<longleftrightarrow> (0 :: int) \<le> e_rows e \<and> (0 :: int) \<le> e_cols e \<and> lm_vld (ev_f env1) (e_rows e) (e_cols e) (e_body e)" for env1 e
definition e_mdl :: "env \<Rightarrow> expr \<Rightarrow> int mat"
  where "e_mdl env1 e = lm_mdl_simp (ev_f env1) (e_rows e) (e_cols e) (e_body e)" for env1 e
consts extends1 :: "(int \<Rightarrow> int mat) \<Rightarrow> int \<Rightarrow> int mat \<Rightarrow> int \<Rightarrow> int mat"
axiomatization where extends'def:   "extends1 f c v n = (if \<not>n = c then f n else v)"
  for f :: "int \<Rightarrow> int mat"
  and c :: "int"
  and v :: "int mat"
  and n :: "int"
definition symb_mat :: "int mat \<Rightarrow> int \<Rightarrow> expr"
  where "symb_mat m n = expr'mk (Cons (mono'mk (Cons n (Nil :: int list)) True) (Nil :: mono list)) (rows m) (cols m)" for m n
definition symb_opp :: "expr \<Rightarrow> expr"
  where "symb_opp e = expr'mk (lm_opp (e_body e)) (e_rows e) (e_cols e)" for e
definition symb_add :: "expr \<Rightarrow> expr \<Rightarrow> expr"
  where "symb_add e1 e2 = expr'mk (lm_merge (Nil :: mono list) (e_body e1) (e_body e2)) (e_rows e1) (e_cols e1)" for e1 e2
definition symb_sub :: "expr \<Rightarrow> expr \<Rightarrow> expr"
  where "symb_sub e1 e2 = symb_add e1 (symb_opp e2)" for e1 e2
definition symb_mul :: "expr \<Rightarrow> expr \<Rightarrow> expr"
  where "symb_mul e1 e2 = expr'mk (lm_distribute (e_body e1) (e_body e2)) (e_rows e1) (e_cols e2)" for e1 e2
end
