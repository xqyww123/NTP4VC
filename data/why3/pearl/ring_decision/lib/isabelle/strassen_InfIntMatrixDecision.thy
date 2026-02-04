theory strassen_InfIntMatrixDecision
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_Sum" "../../lib/isabelle/strassen_Sum_extended" "../../lib/isabelle/strassen_MaxFun" "../../lib/isabelle/strassen_InfIntMatrix"
begin
axiomatization where Assoc:   "x + y + z = x + (y + z)"
  for x :: "int"
  and y :: "int"
  and z :: "int"
axiomatization where Unit_def_l:   "(0 :: int) + x = x"
  for x :: "int"
axiomatization where Unit_def_r:   "x + (0 :: int) = x"
  for x :: "int"
axiomatization where Inv_def_l:   "-x + x = (0 :: int)"
  for x :: "int"
axiomatization where Inv_def_r:   "x + -x = (0 :: int)"
  for x :: "int"
axiomatization where Comm:   "x + y = y + x"
  for x :: "int"
  and y :: "int"
axiomatization where Assoc1:   "x * y * z = x * (y * z)"
  for x :: "int"
  and y :: "int"
  and z :: "int"
axiomatization where Mul_distr_l:   "x * (y + z) = x * y + x * z"
  for x :: "int"
  and y :: "int"
  and z :: "int"
axiomatization where Mul_distr_r:   "(y + z) * x = y * x + z * x"
  for y :: "int"
  and z :: "int"
  and x :: "int"
axiomatization where Comm1:   "x * y = y * x"
  for x :: "int"
  and y :: "int"
axiomatization where Unitary:   "(1 :: int) * x = x"
  for x :: "int"
axiomatization where NonTrivialRing:   "\<not>(0 :: int) = (1 :: int)"
datatype  t = Var "int" | Add "t" "t" | Mul "t" "t" | Ext "int" "t" | Sub "t" "t"
typedecl  vars
fun interp :: "t \<Rightarrow> (int \<Rightarrow> mat) \<Rightarrow> mat"
  where "interp (Var n) y = y n" for n y
      | "interp (Add x1 x2) y = add (interp x1 y) (interp x2 y)" for x1 x2 y
      | "interp (Mul x1 x2) y = mul (interp x1 y) (interp x2 y)" for x1 x2 y
      | "interp (Sub x1 x2) y = sub (interp x1 y) (interp x2 y)" for x1 x2 y
      | "interp (Ext r x1) y = extp r (interp x1 y)" for r x1 y
definition eq :: "t \<Rightarrow> t \<Rightarrow> _"
  where "eq x1 x2 \<longleftrightarrow> (\<forall>(y :: int \<Rightarrow> mat). interp x1 y = interp x2 y)" for x1 x2
datatype  m = M "int" "int list"
typedecl  t'
fun mon :: "int list \<Rightarrow> (int \<Rightarrow> mat) \<Rightarrow> mat"
  where "mon (Nil :: int list) y = id1" for y
      | "mon (Cons x1 l) y = mul (y x1) (mon l y)" for x1 l y
fun interp' :: "m list \<Rightarrow> (int \<Rightarrow> mat) \<Rightarrow> mat"
  where "interp' (Nil :: m list) y = mzero" for y
      | "interp' (Cons (M r m1) l) y = add (extp r (mon m1 y)) (interp' l y)" for r m1 l y
definition eq_mon :: "int list \<Rightarrow> int list \<Rightarrow> _"
  where "eq_mon m1 m2 \<longleftrightarrow> (\<forall>(y :: int \<Rightarrow> mat). mon m1 y = mon m2 y)" for m1 m2
definition eq' :: "m list \<Rightarrow> m list \<Rightarrow> _"
  where "eq' x1 x2 \<longleftrightarrow> (\<forall>(y :: int \<Rightarrow> mat). interp' x1 y = interp' x2 y)" for x1 x2
definition append_mon :: "m \<Rightarrow> m \<Rightarrow> m"
  where "append_mon m1 m2 = (case (m1, m2) of (M r1 l1, M r2 l2) \<Rightarrow> M (r1 * r2) (l1 @ l2))" for m1 m2
axiomatization where append_mon'spec:   "interp' (Cons (append_mon m1 m2) (Nil :: m list)) y = mul (interp' (Cons m1 (Nil :: m list)) y) (interp' (Cons m2 (Nil :: m list)) y)"
  for m1 :: "m"
  and m2 :: "m"
  and y :: "int \<Rightarrow> mat"
fun mul_mon :: "m \<Rightarrow> m list \<Rightarrow> m list"
  where "mul_mon mon1 (Nil :: m list) = (Nil :: m list)" for mon1
      | "mul_mon mon1 (Cons m1 l) = Cons (append_mon mon1 m1) (mul_mon mon1 l)" for mon1 m1 l
axiomatization where mul_mon'spec:   "interp' (mul_mon mon1 x) y = mul (interp' (Cons mon1 (Nil :: m list)) y) (interp' x y)"
  for mon1 :: "m"
  and x :: "m list"
  and y :: "int \<Rightarrow> mat"
fun mul_devel :: "m list \<Rightarrow> m list \<Rightarrow> m list"
  where "mul_devel (Nil :: m list) x2 = (Nil :: m list)" for x2
      | "mul_devel (Cons (M r m1) l) x2 = mul_mon (M r m1) x2 @ mul_devel l x2" for r m1 l x2
axiomatization where mul_devel'spec:   "interp' (mul_devel x1 x2) y = mul (interp' x1 y) (interp' x2 y)"
  for x1 :: "m list"
  and x2 :: "m list"
  and y :: "int \<Rightarrow> mat"
fun ext :: "int \<Rightarrow> m list \<Rightarrow> m list"
  where "ext c (Nil :: m list) = (Nil :: m list)" for c
      | "ext c (Cons (M r m1) l) = Cons (M (c * r) m1) (ext c l)" for c r m1 l
axiomatization where ext'spec:   "interp' (ext c x) y = extp c (interp' x y)"
  for c :: "int"
  and x :: "m list"
  and y :: "int \<Rightarrow> mat"
fun conv :: "t \<Rightarrow> m list"
  where "conv (Var v) = Cons (M (1 :: int) (Cons v (Nil :: int list))) (Nil :: m list)" for v
      | "conv (Add x1 x2) = conv x1 @ conv x2" for x1 x2
      | "conv (Mul x1 x2) = mul_devel (conv x1) (conv x2)" for x1 x2
      | "conv (Ext r x1) = ext r (conv x1)" for r x1
      | "conv (Sub x1 x2) = conv x1 @ ext (-(1 :: int)) (conv x2)" for x1 x2
axiomatization where conv'spec:   "interp x y = interp' (conv x) y"
  for x :: "t"
  and y :: "int \<Rightarrow> mat"
fun le_mon :: "int list \<Rightarrow> int list \<Rightarrow> bool"
  where "le_mon (Nil :: int list) x = (if length (Nil :: int list) < length x then True else if length (Nil :: int list) = length x then True else False)" for x
      | "le_mon x (Nil :: int list) = (if length x < length (Nil :: int list) then True else False)" for x
      | "le_mon (Cons v1 r1) (Cons v2 r2) = (if length (Cons v1 r1) < length (Cons v2 r2) then True else if length (Cons v1 r1) = length (Cons v2 r2) then if v1 < v2 then True else if v1 = v2 then le_mon r1 r2 else False else False)" for v1 r1 v2 r2
fun same :: "int list \<Rightarrow> int list \<Rightarrow> bool"
  where "same (Nil :: int list) (Nil :: int list) = True"
      | "same (Nil :: int list) x = False" for x
      | "same x (Nil :: int list) = False" for x
      | "same (Cons x1 l11) (Cons x2 l21) = (if x1 = x2 then same l11 l21 else False)" for x1 l11 x2 l21
axiomatization where same'spec:   "eq_mon l1 l2"
 if "same l1 l2 = True"
  for l1 :: "int list"
  and l2 :: "int list"
fun insert_mon :: "m \<Rightarrow> m list \<Rightarrow> m list"
  where "insert_mon x (Nil :: m list) = Cons x (Nil :: m list)" for x
      | "insert_mon (M r1 l1) (Cons (M r2 l2) l) = (if same l1 l2 = True then let s :: int = r1 + r2 in if s = (0 :: int) then l else Cons (M s l1) l else if le_mon l1 l2 = True then Cons (M r1 l1) (Cons (M r2 l2) l) else Cons (M r2 l2) (insert_mon (M r1 l1) l))" for r1 l1 r2 l2 l
axiomatization where insert_mon'spec:   "eq' (insert_mon m1 x) (Cons m1 x)"
  for m1 :: "m"
  and x :: "m list"
fun insertion_sort_mon :: "m list \<Rightarrow> m list"
  where "insertion_sort_mon (Nil :: m list) = (Nil :: m list)"
      | "insertion_sort_mon (Cons m1 l) = insert_mon m1 (insertion_sort_mon l)" for m1 l
axiomatization where insertion_sort_mon'spec:   "eq' (insertion_sort_mon x) x"
  for x :: "m list"
axiomatization where normalize''spec:   "eq' (insertion_sort_mon x) x"
  for x :: "m list"
definition normalize :: "t \<Rightarrow> m list"
  where "normalize x = insertion_sort_mon (conv x)" for x
axiomatization where normalize'spec:   "eq' (normalize x) (conv x)"
  for x :: "t"
end
