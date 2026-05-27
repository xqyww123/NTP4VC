theory Functions_Func_const_compose_leftqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.Functions_Config"
begin
definition extensionalEqual :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> _"
  where "extensionalEqual f g \<longleftrightarrow> (\<forall>(x :: 'a). f x = g x)" for f g
axiomatization where functionExtensionality:   "f = g"
 if "extensionalEqual f g"
  for f :: "'a \<Rightarrow> 'b"
  and g :: "'a \<Rightarrow> 'b"
consts update :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b"
axiomatization where update_def:   "update f x y z = (if x = z then y else f z)"
  for f :: "'a \<Rightarrow> 'b"
  and x :: "'a"
  and y :: "'b"
  and z :: "'a"
consts identity :: "'a \<Rightarrow> 'a"
axiomatization where identity_def:   "identity x = x"
  for x :: "'a"
consts compose :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c"
axiomatization where compose_def:   "compose g f x = g (f x)"
  for g :: "'b \<Rightarrow> 'c"
  and f :: "'a \<Rightarrow> 'b"
  and x :: "'a"
consts const :: "'b \<Rightarrow> 'a \<Rightarrow> 'b"
axiomatization where const_def:   "(const :: 'b \<Rightarrow> 'a \<Rightarrow> 'b) x z = x"
  for x :: "'b"
  and z :: "'a"
theorem const_compose_left'vc:
  fixes x :: "'c"
  fixes f :: "'a \<Rightarrow> 'b"
  shows "compose ((const :: 'c \<Rightarrow> 'b \<Rightarrow> 'c) x) f = (const :: 'c \<Rightarrow> 'a \<Rightarrow> 'c) x"
  sorry
end
