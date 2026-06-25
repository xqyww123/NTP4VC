theory verifythis_2018_array_based_queuing_lock_2_ABQL_numof_equivqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_NumOf" "Why3STD.queue_Queue"
begin
consts n :: "int"
axiomatization where N_val:   "(2 :: int) \<le> n"
consts k :: "int"
axiomatization where K_val:   "(2 :: int) \<le> k"
typedecl  tick
consts b :: "tick \<Rightarrow> int"
consts v :: "tick \<Rightarrow> int"
axiomatization where tick'invariant'0:   "(0 :: int) \<le> v self"
  for self :: "tick"
axiomatization where tick'invariant'1:   "(0 :: int) \<le> b self"
  for self :: "tick"
axiomatization where tick'invariant'2:   "b self < k * n"
  for self :: "tick"
axiomatization where tick'invariant'3:   "b self = v self emod (k * n)"
  for self :: "tick"
definition tick'eq :: "tick \<Rightarrow> tick \<Rightarrow> _"
  where "tick'eq a b1 \<longleftrightarrow> b a = b b1 \<and> v a = v b1" for a b1
axiomatization where tick'inj:   "a = b1"
 if "tick'eq a b1"
  for a :: "tick"
  and b1 :: "tick"
definition lt :: "tick \<Rightarrow> tick \<Rightarrow> _"
  where "lt tick1 tick2 \<longleftrightarrow> v tick1 < v tick2" for tick1 tick2
definition sorted :: "tick list \<Rightarrow> _"
  where "sorted s \<longleftrightarrow> (\<forall>(i :: int) (j :: int). (0 :: int) \<le> i \<and> i < j \<and> j < int (length s) \<longrightarrow> lt (s ! nat i) (s ! nat j))" for s
definition consecutive :: "tick list \<Rightarrow> _"
  where "consecutive l \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) < i \<and> i < int (length l) \<longrightarrow> v (l ! nat i) = v (l ! nat (i - (1 :: int))) + (1 :: int))" for l
definition last :: "tick list \<Rightarrow> tick option"
  where "last l = (if int (length l) = (0 :: int) then None else Some (l ! nat (int (length l) - (1 :: int))))" for l
definition hd :: "tick list \<Rightarrow> tick option"
  where "hd l = (if int (length l) = (0 :: int) then None else Some (l ! (0 :: nat)))" for l
datatype  pc = A1 | A2 | A3 | R1 | R2 | I | W
definition has_ticket :: "pc \<Rightarrow> _"
  where "has_ticket pc1 \<longleftrightarrow> (case pc1 of A1 \<Rightarrow> False | I \<Rightarrow> False | _ \<Rightarrow> True)" for pc1
definition has_lock :: "pc \<Rightarrow> _"
  where "has_lock pc1 \<longleftrightarrow> (case pc1 of A3 \<Rightarrow> True | W \<Rightarrow> True | R1 \<Rightarrow> True | R2 \<Rightarrow> True | _ \<Rightarrow> False)" for pc1
typedecl  nondet_source
typedecl  rng
consts source :: "rng \<Rightarrow> nondet_source"
consts fc :: "'a list \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> bool"
axiomatization where fc_def:   "fc a v1 i = True \<longleftrightarrow> a ! nat i = v1"
  for a :: "'a list"
  and v1 :: "'a"
  and i :: "int"
theorem numof_equiv'vc:
  fixes l :: "int"
  fixes u :: "int"
  fixes a1 :: "'a list"
  fixes v1 :: "'a"
  fixes a2 :: "'a list"
  assumes fact0: "\<forall>(i :: int). l \<le> i \<and> i < u \<longrightarrow> a1 ! nat i = v1 \<longleftrightarrow> a2 ! nat i = v1"
  shows "count_list (take (nat u - nat l) (drop (nat l) a1)) v1 = count_list (take (nat u - nat l) (drop (nat l) a2)) v1"
  sorry
end
