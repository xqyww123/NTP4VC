theory ccursor_PtrCursor
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C"
begin
typedecl  cursor
consts current :: "cursor \<Rightarrow> 32 word ptr"
consts new :: "cursor \<Rightarrow> bool"
consts len :: "cursor \<Rightarrow> 32 word"
consts freed :: "cursor \<Rightarrow> bool"
consts bound :: "cursor \<Rightarrow> 32 word"
axiomatization where cursor'invariant'0:   "(0 :: int) < sint (len self)"
  for self :: "cursor"
axiomatization where cursor'invariant'1:   "\<not>freed self = True \<longrightarrow> plength (current self) = sint (len self) \<and> offset (current self) = (0 :: int) \<and> valid (current self) (sint (len self)) \<and> c_C.min (current self) = (0 :: int) \<and> c_C.max (current self) = sint (len self) \<and> is_not_null (current self) \<and> writable (current self) = True \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < sint (len self) \<longrightarrow> sint (data (current self) ! nat i) < sint (bound self))"
  for self :: "cursor"
definition cursor'eq :: "cursor \<Rightarrow> cursor \<Rightarrow> _"
  where "cursor'eq a b \<longleftrightarrow> current a = current b \<and> new a = new b \<and> len a = len b \<and> freed a = freed b \<and> bound a = bound b" for a b
axiomatization where cursor'inj:   "a = b"
 if "cursor'eq a b"
  for a :: "cursor"
  and b :: "cursor"
end
