theory dict_Imperative
  imports "NTP4Verif.NTP4Verif"
begin
typedecl ('key, 'value) model
typedecl ('key, 'value) t
consts model1 :: "('key, 'value) t \<Rightarrow> 'key \<Rightarrow> 'value option"
definition get :: "('key, 'value) t \<Rightarrow> 'key \<Rightarrow> 'value option"
  where "get d k = model1 d k" for d k
end
