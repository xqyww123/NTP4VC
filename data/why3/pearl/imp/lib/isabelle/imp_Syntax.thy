theory imp_Syntax
  imports "NTP4Verif.NTP4Verif"
begin
typedecl  program_var
datatype  expr = Elit "int" | Evar "program_var" | Esub "expr" "expr"
datatype  cmd = Cskip | Cassign "program_var" "expr" | Cseq "cmd" "cmd" | Cif "expr" "cmd" "cmd" | Cwhile "expr" "cmd"
end
