theory ral_RAL_selected_partqtvc
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
theorem selected_part'vc:
  fixes s :: "selector"
  fixes lseq :: "'a list"
  fixes d :: "'a"
  fixes rseq :: "'a list"
  assumes fact0: "selection_possible s (lseq @ Cons d rseq)"
  shows "let ind :: int = index s in \<forall>(result :: selector part_base). (if int (length lseq) < ind then result = Right (selector'mk (ind - int (length lseq) - (1 :: int)) (hole s)) else if ind < int (length lseq) then result = Left s else if hole s = True then result = Left s else result = Here) \<longrightarrow> (case result of Here \<Rightarrow> selected s (split'mk lseq (Some d) rseq) | Left rsl \<Rightarrow> selection_possible rsl lseq \<and> (\<forall>(e :: 'a split). selected rsl e \<and> rebuild e = lseq \<longrightarrow> selected s (right_extend e d rseq)) | Right rsr \<Rightarrow> selection_possible rsr rseq \<and> (\<forall>(e :: 'a split). selected rsr e \<and> rebuild e = rseq \<longrightarrow> selected s (left_extend lseq d e)))"
  sorry
end
