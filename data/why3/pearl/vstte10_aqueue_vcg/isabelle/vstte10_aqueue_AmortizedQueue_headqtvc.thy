theory vstte10_aqueue_AmortizedQueue_headqtvc
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
theorem head'vc:
  fixes q :: "'a queue"
  assumes fact0: "\<not>sequence q = (Nil :: 'a list)"
  shows "let o1 :: 'a list = front q in (case o1 of Cons x _ \<Rightarrow> True | _ \<Rightarrow> False) \<and> (\<forall>(result :: 'a). (case o1 of Cons x _ \<Rightarrow> result = x | _ \<Rightarrow> False) \<longrightarrow> (if sequence q = Nil then None else Some (hd (sequence q))) = Some result)"
  sorry
end
