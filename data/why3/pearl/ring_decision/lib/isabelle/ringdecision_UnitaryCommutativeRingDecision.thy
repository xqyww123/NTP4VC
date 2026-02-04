theory ringdecision_UnitaryCommutativeRingDecision
  imports "NTP4Verif.NTP4Verif"
begin
typedecl  t
consts zero :: "t"
consts infix_pl :: "t \<Rightarrow> t \<Rightarrow> t"
consts prefix_mn :: "t \<Rightarrow> t"
consts infix_as :: "t \<Rightarrow> t \<Rightarrow> t"
axiomatization where Assoc:   "infix_pl (infix_pl x y) z = infix_pl x (infix_pl y z)"
  for x :: "t"
  and y :: "t"
  and z :: "t"
axiomatization where Unit_def_l:   "infix_pl zero x = x"
  for x :: "t"
axiomatization where Unit_def_r:   "infix_pl x zero = x"
  for x :: "t"
axiomatization where Inv_def_l:   "infix_pl (prefix_mn x) x = zero"
  for x :: "t"
axiomatization where Inv_def_r:   "infix_pl x (prefix_mn x) = zero"
  for x :: "t"
axiomatization where Comm:   "infix_pl x y = infix_pl y x"
  for x :: "t"
  and y :: "t"
axiomatization where Assoc1:   "infix_as (infix_as x y) z = infix_as x (infix_as y z)"
  for x :: "t"
  and y :: "t"
  and z :: "t"
axiomatization where Mul_distr_l:   "infix_as x (infix_pl y z) = infix_pl (infix_as x y) (infix_as x z)"
  for x :: "t"
  and y :: "t"
  and z :: "t"
axiomatization where Mul_distr_r:   "infix_as (infix_pl y z) x = infix_pl (infix_as y x) (infix_as z x)"
  for y :: "t"
  and z :: "t"
  and x :: "t"
axiomatization where Comm1:   "infix_as x y = infix_as y x"
  for x :: "t"
  and y :: "t"
consts one :: "t"
axiomatization where Unitary:   "infix_as one x = x"
  for x :: "t"
axiomatization where NonTrivialRing:   "\<not>zero = one"
typedecl  t1
consts zero1 :: "t1"
consts infix_pl' :: "t1 \<Rightarrow> t1 \<Rightarrow> t1"
consts prefix_mn' :: "t1 \<Rightarrow> t1"
consts infix_as' :: "t1 \<Rightarrow> t1 \<Rightarrow> t1"
axiomatization where Assoc2:   "infix_pl' (infix_pl' x y) z = infix_pl' x (infix_pl' y z)"
  for x :: "t1"
  and y :: "t1"
  and z :: "t1"
axiomatization where Unit_def_l1:   "infix_pl' zero1 x = x"
  for x :: "t1"
axiomatization where Unit_def_r1:   "infix_pl' x zero1 = x"
  for x :: "t1"
axiomatization where Inv_def_l1:   "infix_pl' (prefix_mn' x) x = zero1"
  for x :: "t1"
axiomatization where Inv_def_r1:   "infix_pl' x (prefix_mn' x) = zero1"
  for x :: "t1"
axiomatization where Comm2:   "infix_pl' x y = infix_pl' y x"
  for x :: "t1"
  and y :: "t1"
axiomatization where Assoc3:   "infix_as' (infix_as' x y) z = infix_as' x (infix_as' y z)"
  for x :: "t1"
  and y :: "t1"
  and z :: "t1"
axiomatization where Mul_distr_l1:   "infix_as' x (infix_pl' y z) = infix_pl' (infix_as' x y) (infix_as' x z)"
  for x :: "t1"
  and y :: "t1"
  and z :: "t1"
axiomatization where Mul_distr_r1:   "infix_as' (infix_pl' y z) x = infix_pl' (infix_as' y x) (infix_as' z x)"
  for y :: "t1"
  and z :: "t1"
  and x :: "t1"
axiomatization where Comm3:   "infix_as' x y = infix_as' y x"
  for x :: "t1"
  and y :: "t1"
consts one1 :: "t1"
axiomatization where Unitary1:   "infix_as' one1 x = x"
  for x :: "t1"
axiomatization where NonTrivialRing1:   "\<not>zero1 = one1"
consts morph :: "t1 \<Rightarrow> t"
axiomatization where morph_zero:   "morph zero1 = zero"
axiomatization where morph_one:   "morph one1 = one"
axiomatization where morph_add:   "morph (infix_pl' z1 z2) = infix_pl (morph z1) (morph z2)"
  for z1 :: "t1"
  and z2 :: "t1"
axiomatization where morph_mul:   "morph (infix_as' z1 z2) = infix_as (morph z1) (morph z2)"
  for z1 :: "t1"
  and z2 :: "t1"
axiomatization where morph_inv:   "morph (prefix_mn' z) = prefix_mn (morph z)"
  for z :: "t1"
consts eq0 :: "t1 \<Rightarrow> bool"
axiomatization where eq0'spec:   "eq0 x \<longleftrightarrow> x = zero1"
  for x :: "t1"
datatype  t2 = Var "int" | Add "t2" "t2" | Mul "t2" "t2" | Cst "t1"
typedecl  vars
fun interp :: "t2 \<Rightarrow> (int \<Rightarrow> t) \<Rightarrow> t"
  where "interp (Var n) y = y n" for n y
      | "interp (Add x1 x2) y = infix_pl (interp x1 y) (interp x2 y)" for x1 x2 y
      | "interp (Mul x1 x2) y = infix_as (interp x1 y) (interp x2 y)" for x1 x2 y
      | "interp (Cst c) y = morph c" for c y
definition eq :: "t2 \<Rightarrow> t2 \<Rightarrow> _"
  where "eq x1 x2 \<longleftrightarrow> (\<forall>(y :: int \<Rightarrow> t). interp x1 y = interp x2 y)" for x1 x2
datatype  m = M "t1" "int list"
typedecl  t'
fun mon :: "int list \<Rightarrow> (int \<Rightarrow> t) \<Rightarrow> t"
  where "mon (Nil :: int list) y = one" for y
      | "mon (Cons x1 r) y = infix_as (y x1) (mon r y)" for x1 r y
fun interp' :: "m list \<Rightarrow> (int \<Rightarrow> t) \<Rightarrow> t"
  where "interp' (Nil :: m list) y = zero" for y
      | "interp' (Cons (M a m1) r) y = infix_pl (infix_as (morph a) (mon m1 y)) (interp' r y)" for a m1 r y
definition eq_mon :: "int list \<Rightarrow> int list \<Rightarrow> _"
  where "eq_mon m1 m2 \<longleftrightarrow> (\<forall>(y :: int \<Rightarrow> t). mon m1 y = mon m2 y)" for m1 m2
definition eq' :: "m list \<Rightarrow> m list \<Rightarrow> _"
  where "eq' x1 x2 \<longleftrightarrow> (\<forall>(y :: int \<Rightarrow> t). interp' x1 y = interp' x2 y)" for x1 x2
definition append_mon :: "m \<Rightarrow> m \<Rightarrow> m"
  where "append_mon m1 m2 = (case (m1, m2) of (M a1 l1, M a2 l2) \<Rightarrow> M (infix_as' a1 a2) (l1 @ l2))" for m1 m2
axiomatization where append_mon'spec:   "interp' (Cons (append_mon m1 m2) (Nil :: m list)) y = infix_as (interp' (Cons m1 (Nil :: m list)) y) (interp' (Cons m2 (Nil :: m list)) y)"
  for m1 :: "m"
  and m2 :: "m"
  and y :: "int \<Rightarrow> t"
fun mul_mon :: "m list \<Rightarrow> m \<Rightarrow> m list"
  where "mul_mon (Nil :: m list) mon1 = (Nil :: m list)" for mon1
      | "mul_mon (Cons m1 r) mon1 = Cons (append_mon m1 mon1) (mul_mon r mon1)" for m1 r mon1
axiomatization where mul_mon'spec:   "interp' (mul_mon x mon1) y = infix_as (interp' x y) (interp' (Cons mon1 (Nil :: m list)) y)"
  for x :: "m list"
  and mon1 :: "m"
  and y :: "int \<Rightarrow> t"
fun mul_devel :: "m list \<Rightarrow> m list \<Rightarrow> m list"
  where "mul_devel (Nil :: m list) x2 = (Nil :: m list)" for x2
      | "mul_devel (Cons (M a m1) r) x2 = mul_mon x2 (M a m1) @ mul_devel r x2" for a m1 r x2
axiomatization where mul_devel'spec:   "interp' (mul_devel x1 x2) y = infix_as (interp' x1 y) (interp' x2 y)"
  for x1 :: "m list"
  and x2 :: "m list"
  and y :: "int \<Rightarrow> t"
fun conv :: "t2 \<Rightarrow> m list"
  where "conv (Var v) = Cons (M one1 (Cons v (Nil :: int list))) (Nil :: m list)" for v
      | "conv (Add x1 x2) = conv x1 @ conv x2" for x1 x2
      | "conv (Mul x1 x2) = mul_devel (conv x1) (conv x2)" for x1 x2
      | "conv (Cst n) = Cons (M n (Nil :: int list)) (Nil :: m list)" for n
axiomatization where conv'spec:   "interp x y = interp' (conv x) y"
  for x :: "t2"
  and y :: "int \<Rightarrow> t"
fun insert :: "int \<Rightarrow> int list \<Rightarrow> int list"
  where "insert x (Nil :: int list) = Cons x (Nil :: int list)" for x
      | "insert x (Cons y r) = (if x \<le> y then Cons x (Cons y r) else Cons y (insert x r))" for x y r
axiomatization where insert'spec:   "eq_mon (Cons x l) (insert x l)"
  for x :: "int"
  and l :: "int list"
fun insertion_sort :: "int list \<Rightarrow> int list"
  where "insertion_sort (Nil :: int list) = (Nil :: int list)"
      | "insertion_sort (Cons x r) = insert x (insertion_sort r)" for x r
axiomatization where insertion_sort'spec:   "eq_mon l (insertion_sort l)"
  for l :: "int list"
definition sort_mon :: "m \<Rightarrow> m"
  where "sort_mon x = (case x of M a m1 \<Rightarrow> M a (insertion_sort m1))" for x
axiomatization where sort_mon'spec:   "eq' (Cons x (Nil :: m list)) (Cons (sort_mon x) (Nil :: m list))"
  for x :: "m"
fun sort_mons :: "m list \<Rightarrow> m list"
  where "sort_mons (Nil :: m list) = (Nil :: m list)"
      | "sort_mons (Cons m1 r) = Cons (sort_mon m1) (sort_mons r)" for m1 r
axiomatization where sort_mons'spec:   "eq' (sort_mons x) x"
  for x :: "m list"
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
      | "insert_mon (M a1 l1) (Cons (M a2 l2) r) = (if same l1 l2 = True then let s :: t1 = infix_pl' a1 a2 in if eq0 s then r else Cons (M s l1) r else if le_mon l1 l2 = True then Cons (M a1 l1) (Cons (M a2 l2) r) else Cons (M a2 l2) (insert_mon (M a1 l1) r))" for a1 l1 a2 l2 r
axiomatization where insert_mon'spec:   "eq' (insert_mon m1 x) (Cons m1 x)"
  for m1 :: "m"
  and x :: "m list"
fun insertion_sort_mon :: "m list \<Rightarrow> m list"
  where "insertion_sort_mon (Nil :: m list) = (Nil :: m list)"
      | "insertion_sort_mon (Cons m1 r) = insert_mon m1 (insertion_sort_mon r)" for m1 r
axiomatization where insertion_sort_mon'spec:   "eq' (insertion_sort_mon x) x"
  for x :: "m list"
definition normalize :: "m list \<Rightarrow> m list"
  where "normalize x = insertion_sort_mon (sort_mons x)" for x
axiomatization where normalize'spec:   "eq' (normalize x) x"
  for x :: "m list"
end
