theory imp_SymState_mk_sym_stateqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_imp_lib.imp_Syntax" "pearl_imp_lib.imp_Svar" "pearl_imp_lib.imp_Constraint"
begin
typedecl  sym_state
consts sigma :: "sym_state \<Rightarrow> t"
consts constr :: "sym_state \<Rightarrow> constr"
consts rho :: "sym_state \<Rightarrow> svar \<Rightarrow> int"
consts vars :: "sym_state \<Rightarrow> imp_Svar.set"
axiomatization where sym_state'invariant'0:   "vars_in_constraint (constr self) |\<subseteq>| to_fset (vars self)"
  for self :: "sym_state"
axiomatization where sym_state'invariant'1:   "\<forall>(x :: program_var) (v :: svar). get (sigma self) x = Some v \<longrightarrow> v |\<in>| to_fset (vars self)"
  for self :: "sym_state"
definition sym_state'eq :: "sym_state \<Rightarrow> sym_state \<Rightarrow> _"
  where "sym_state'eq a b \<longleftrightarrow> sigma a = sigma b \<and> constr a = constr b \<and> rho a = rho b \<and> vars a = vars b" for a b
axiomatization where sym_state'inj:   "a = b"
 if "sym_state'eq a b"
  for a :: "sym_state"
  and b :: "sym_state"
consts eq :: "sym_state \<Rightarrow> sym_state \<Rightarrow> bool"
axiomatization where eq'spec:   "eq s1 s2 \<longleftrightarrow> s1 = s2"
  for s1 :: "sym_state"
  and s2 :: "sym_state"
theorem mk_sym_state'vc:
  fixes constr1 :: "constr"
  fixes vars1 :: "imp_Svar.set"
  fixes sigma1 :: "t"
  fixes rho1 :: "svar \<Rightarrow> int"
  assumes fact0: "vars_in_constraint constr1 |\<subseteq>| to_fset vars1"
  assumes fact1: "\<forall>(x :: program_var) (v :: svar). get sigma1 x = Some v \<longrightarrow> v |\<in>| to_fset vars1"
  shows "vars_in_constraint constr1 |\<subseteq>| to_fset vars1"
  and "\<forall>(x :: program_var) (v :: svar). get sigma1 x = Some v \<longrightarrow> v |\<in>| to_fset vars1"
  and "\<forall>(result :: sym_state). sigma result = sigma1 \<and> constr result = constr1 \<and> rho result = rho1 \<and> vars result = vars1 \<longrightarrow> sigma result = sigma1 \<and> constr result = constr1 \<and> vars result = vars1 \<and> rho result = rho1"
  sorry
end
