theory avl_SelectionTypes
  imports "NTP4Verif.NTP4Verif"
begin
datatype 'a split = split'mk (left1: "'a list") (middle: "'a option") (right1: "'a list")
datatype 'a part_base = Left "'a" | Right "'a" | Here
definition option_to_seq :: "'a option \<Rightarrow> 'a list"
  where "option_to_seq o1 = (case o1 of Some x \<Rightarrow> [x] | (None :: 'a option) \<Rightarrow> ([] :: 'a list))" for o1
definition rebuild :: "'a split \<Rightarrow> 'a list"
  where "rebuild p = (left1 p @ option_to_seq (middle p)) @ right1 p" for p
definition left_extend :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a split \<Rightarrow> 'a split"
  where "left_extend l d e = split'mk (l @ Cons d (left1 e)) (middle e) (right1 e)" for l d e
definition right_extend :: "'a split \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a split"
  where "right_extend e d r = split'mk (left1 e) (middle e) (right1 e @ Cons d r)" for e d r
end
