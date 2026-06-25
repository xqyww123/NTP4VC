theory verifythis_2018_array_based_queuing_lock_1_Top_zeroqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
consts k :: "int"
axiomatization where k_def:   "(0 :: int) < k"
consts n :: "int"
axiomatization where n_def:   "(0 :: int) < n"
typedecl  bounded_int
consts bmodel :: "bounded_int \<Rightarrow> int"
axiomatization where bounded_int'invariant'0:   "(0 :: int) \<le> bmodel self"
  for self :: "bounded_int"
axiomatization where bounded_int'invariant'1:   "bmodel self < k * n"
  for self :: "bounded_int"
consts bzero :: "bounded_int"
axiomatization where bmodel_def:   "bmodel bzero = (0 :: int)"
typedecl  bounded_int2
consts "value" :: "bounded_int2 \<Rightarrow> bounded_int"
consts model :: "bounded_int2 \<Rightarrow> int"
axiomatization where bounded_int2'invariant'0:   "(0 :: int) \<le> model self"
  for self :: "bounded_int2"
axiomatization where bounded_int2'invariant'1:   "model self < n"
  for self :: "bounded_int2"
axiomatization where bounded_int2'invariant'2:   "model self = bmodel (value self) cmod n"
  for self :: "bounded_int2"
definition bounded_int2'eq :: "bounded_int2 \<Rightarrow> bounded_int2 \<Rightarrow> _"
  where "bounded_int2'eq a b \<longleftrightarrow> value a = value b \<and> model a = model b" for a b
axiomatization where bounded_int2'inj:   "a = b"
 if "bounded_int2'eq a b"
  for a :: "bounded_int2"
  and b :: "bounded_int2"
typedecl  ticket
consts tvalue :: "ticket \<Rightarrow> int"
axiomatization where ticket'invariant'0:   "(0 :: int) \<le> tvalue self"
  for self :: "ticket"
axiomatization where ticket'invariant'1:   "tvalue self < n"
  for self :: "ticket"
definition ticket'eq :: "ticket \<Rightarrow> ticket \<Rightarrow> _"
  where "ticket'eq a b \<longleftrightarrow> tvalue a = tvalue b" for a b
axiomatization where ticket'inj:   "a = b"
 if "ticket'eq a b"
  for a :: "ticket"
  and b :: "ticket"
theorem zero'vc:
  shows "let o1 :: bounded_int = bzero in (((0 :: int) \<le> (0 :: int) \<and> (0 :: int) < n) \<and> (0 :: int) = bmodel o1 cmod n) \<and> (\<forall>(result :: bounded_int2). value result = o1 \<and> model result = (0 :: int) \<longrightarrow> model result = (0 :: int))"
  sorry
end
