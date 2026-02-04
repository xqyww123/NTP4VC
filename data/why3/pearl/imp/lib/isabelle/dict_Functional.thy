theory dict_Functional
  imports "NTP4Verif.NTP4Verif"
begin
typedecl  key
typedecl  "value"
typedecl  model
typedecl  t
consts model1 :: "t \<Rightarrow> key \<Rightarrow> value option"
consts empty :: "t"
axiomatization where empty1:   "model1 empty k = None"
  for k :: "key"
definition get :: "t \<Rightarrow> key \<Rightarrow> value option"
  where "get d k = model1 d k" for d k
consts set :: "t \<Rightarrow> key \<Rightarrow> value \<Rightarrow> t"
axiomatization where set'spec'0:   "get (set d k v) k = Some v"
  for d :: "t"
  and k :: "key"
  and v :: "value"
axiomatization where set'spec:   "get (set d k v) k' = get d k'"
 if "\<not>k' = k"
  for k' :: "key"
  and k :: "key"
  and d :: "t"
  and v :: "value"
end
