theory vstte10_aqueue_AmortizedQueue_createqtvc
  imports "NTP4Verif.NTP4Verif"
begin
typedecl 'a queue
consts front :: "'a queue \<Rightarrow> 'a list"
consts lenf :: "'a queue \<Rightarrow> int"
consts rear :: "'a queue \<Rightarrow> 'a list"
consts lenr :: "'a queue \<Rightarrow> int"
axiomatization where queue'invariant'0:   "int (length (front self)) = lenf self"
  for self :: "'a queue"
axiomatization where queue'invariant'1:   "int (length (rear self)) \<le> lenf self"
  for self :: "'a queue"
axiomatization where queue'invariant'2:   "int (length (rear self)) = lenr self"
  for self :: "'a queue"
definition queue'eq :: "'a queue \<Rightarrow> 'a queue \<Rightarrow> _"
  where "queue'eq a b \<longleftrightarrow> front a = front b \<and> lenf a = lenf b \<and> rear a = rear b \<and> lenr a = lenr b" for a b
axiomatization where queue'inj:   "a = b"
 if "queue'eq a b"
  for a :: "'a queue"
  and b :: "'a queue"
definition sequence :: "'a queue \<Rightarrow> 'a list"
  where "sequence q = front q @ rev (rear q)" for q
consts empty :: "'a queue"
axiomatization where empty_def:   "sequence (empty :: 'a queue) = (Nil :: 'a list)"
theorem create'vc:
  fixes r :: "'a list"
  fixes f :: "'a list"
  shows "if length r \<le> length f then length r \<le> length f else let o1 :: 'a list = (Nil :: 'a list); o2 :: int = int (length f) + int (length r) in int (length (f @ rev r)) = o2 \<and> int (length o1) \<le> o2 \<and> int (length o1) = (0 :: int)"
  and "\<forall>(result :: 'a queue). (if length r \<le> length f then front result = f \<and> lenf result = int (length f) \<and> rear result = r \<and> lenr result = int (length r) else front result = f @ rev r \<and> lenf result = int (length f) + int (length r) \<and> rear result = (Nil :: 'a list) \<and> lenr result = (0 :: int)) \<longrightarrow> sequence result = f @ rev r"
  sorry
end
