theory vstte10_aqueue_AmortizedQueue_enqueueqtvc
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
theorem enqueue'vc:
  fixes x :: "'a"
  fixes q :: "'a queue"
  shows "let o1 :: 'a list = Cons x (rear q); o2 :: 'a list = front q in (lenf q = int (length o2) \<and> lenr q + (1 :: int) = int (length o1)) \<and> (\<forall>(result :: 'a queue). sequence result = o2 @ rev o1 \<longrightarrow> sequence result = sequence q @ Cons x (Nil :: 'a list))"
  sorry
end
