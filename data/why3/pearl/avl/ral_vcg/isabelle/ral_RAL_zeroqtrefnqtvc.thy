theory ral_RAL_zeroqtrefnqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_avl_lib.avl_SelectionTypes"
begin
consts balancing :: "nat"
axiomatization where balancing'def:   "(0 :: int) < int balancing"
typedecl  m
typedecl  t
axiomatization where assoc:   "a + (b + c) = a + b + c"
  for a :: "int"
  and b :: "int"
  and c :: "int"
axiomatization where neutral'0:   "x + (0 :: int) = x"
  for x :: "int"
axiomatization where neutral'1:   "x = (0 :: int) + x"
  for x :: "int"
consts agg :: "('a \<Rightarrow> int) \<Rightarrow> 'a list \<Rightarrow> int"
axiomatization where agg'def:   "if int (length s) = (0 :: int) then agg f s = (0 :: int) else agg f s = f (s ! (0 :: nat)) + agg f (drop (1 :: nat) s)"
  for s :: "'a list"
  and f :: "'a \<Rightarrow> int"
typedecl 'a t1
definition measure :: "'a \<Rightarrow> int"
  where "measure x = (1 :: int)" for x
datatype  selector = selector'mk (index: "int") (hole: "bool")
definition selection_possible :: "selector \<Rightarrow> 'a list \<Rightarrow> _"
  where "selection_possible s l \<longleftrightarrow> (0 :: int) \<le> index s \<and> (if hole s = True then index s \<le> int (length l) else index s < int (length l))" for s l
definition selected :: "selector \<Rightarrow> 'a split \<Rightarrow> _"
  where "selected s e \<longleftrightarrow> index s = int (length (left1 e)) \<and> (hole s = True \<longleftrightarrow> middle e = (None :: 'a option))" for s e
theorem zero'refn'vc:
  shows "True"
  sorry
end
