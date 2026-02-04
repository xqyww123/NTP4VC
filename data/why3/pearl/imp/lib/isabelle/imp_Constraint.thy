theory imp_Constraint
  imports "NTP4Verif.NTP4Verif" "../../lib/isabelle/imp_Syntax" "../../lib/isabelle/imp_Svar"
begin
typedecl  model
typedecl  t
consts model1 :: "t \<Rightarrow> program_var \<Rightarrow> svar option"
consts empty :: "t"
axiomatization where empty1:   "model1 empty k = None"
  for k :: "program_var"
definition get :: "t \<Rightarrow> program_var \<Rightarrow> svar option"
  where "get d k = model1 d k" for d k
consts set :: "t \<Rightarrow> program_var \<Rightarrow> svar \<Rightarrow> t"
axiomatization where set'spec'0:   "get (set d k v) k = Some v"
  for d :: "t"
  and k :: "program_var"
  and v :: "svar"
axiomatization where set'spec:   "get (set d k v) k' = get d k'"
 if "\<not>k' = k"
  for k' :: "program_var"
  and k :: "program_var"
  and d :: "t"
  and v :: "svar"
typedecl  rho
datatype  symbolic_expr = Slit "int" | Svar "svar" | Ssub "symbolic_expr" "symbolic_expr"
fun interp_symbolic_expr :: "(svar \<Rightarrow> int) \<Rightarrow> symbolic_expr \<Rightarrow> int"
  where "interp_symbolic_expr rho1 (Slit n) = n" for rho1 n
      | "interp_symbolic_expr rho1 (Svar v) = rho1 v" for rho1 v
      | "interp_symbolic_expr rho1 (Ssub e1 e2) = interp_symbolic_expr rho1 e1 - interp_symbolic_expr rho1 e2" for rho1 e1 e2
datatype  constr = Ctrue | Cfalse | Ceq "symbolic_expr" "symbolic_expr" | Cneq "symbolic_expr" "symbolic_expr" | Cconj "constr" "constr" | Cexists "svar" "constr"
fun is_solution :: "(svar \<Rightarrow> int) \<Rightarrow> constr \<Rightarrow> _"
  where "is_solution rho1 Ctrue = True" for rho1
      | "is_solution rho1 Cfalse = False" for rho1
      | "is_solution rho1 (Ceq e1 e2) = (interp_symbolic_expr rho1 e1 = interp_symbolic_expr rho1 e2)" for rho1 e1 e2
      | "is_solution rho1 (Cneq e1 e2) = (\<not>interp_symbolic_expr rho1 e1 = interp_symbolic_expr rho1 e2)" for rho1 e1 e2
      | "is_solution rho1 (Cconj c1 c2) = (is_solution rho1 c1 \<and> is_solution rho1 c2)" for rho1 c1 c2
      | "is_solution rho1 (Cexists x c1) = is_solution rho1 c1" for rho1 x c1
fun vars_in_symbolic_expr :: "symbolic_expr \<Rightarrow> svar fset"
  where "vars_in_symbolic_expr (Slit x) = fempty" for x
      | "vars_in_symbolic_expr (Svar v) = finsert v fempty" for v
      | "vars_in_symbolic_expr (Ssub e1 e2) = vars_in_symbolic_expr e1 |\<union>| vars_in_symbolic_expr e2" for e1 e2
fun vars_in_constraint :: "constr \<Rightarrow> svar fset"
  where "vars_in_constraint Ctrue = fempty"
      | "vars_in_constraint Cfalse = fempty"
      | "vars_in_constraint (Ceq e1 e2) = vars_in_symbolic_expr e1 |\<union>| vars_in_symbolic_expr e2" for e1 e2
      | "vars_in_constraint (Cneq e1 e2) = vars_in_symbolic_expr e1 |\<union>| vars_in_symbolic_expr e2" for e1 e2
      | "vars_in_constraint (Cconj c1 c2) = vars_in_constraint c1 |\<union>| vars_in_constraint c2" for c1 c2
      | "vars_in_constraint (Cexists v c1) = finsert v (vars_in_constraint c1)" for v c1
fun existential_vars_in_constraint :: "constr \<Rightarrow> svar fset"
  where "existential_vars_in_constraint Ctrue = fempty"
      | "existential_vars_in_constraint Cfalse = fempty"
      | "existential_vars_in_constraint (Ceq e1 e2) = vars_in_symbolic_expr e1 |\<union>| vars_in_symbolic_expr e2" for e1 e2
      | "existential_vars_in_constraint (Cneq e1 e2) = vars_in_symbolic_expr e1 |\<union>| vars_in_symbolic_expr e2" for e1 e2
      | "existential_vars_in_constraint (Cconj c1 c2) = existential_vars_in_constraint c1 |\<union>| existential_vars_in_constraint c2" for c1 c2
      | "existential_vars_in_constraint (Cexists v c1) = fset_remove v (existential_vars_in_constraint c1)" for v c1
definition free_vars_in_constraint :: "constr \<Rightarrow> svar fset"
  where "free_vars_in_constraint c = vars_in_constraint c |-| existential_vars_in_constraint c" for c
definition entails :: "constr \<Rightarrow> constr \<Rightarrow> _"
  where "entails c1 c2 \<longleftrightarrow> (\<forall>(rho1 :: svar \<Rightarrow> int). is_solution rho1 c1 \<longrightarrow> is_solution rho1 c2)" for c1 c2
end
