theory BacktrackArray_Types
  imports "NTP4Verif.NTP4Verif" "../../lib/isabelle/Functions_Config" "../../lib/isabelle/Functions_Func" "../../lib/isabelle/Predicates_Pred"
begin
datatype 'a timestamp = timestamp'mk (time: "int") (size: "int") (table: "int \<Rightarrow> 'a list")
datatype 'a t = t'mk (history: "int list") (current_time: "int") (buffer: "'a list list") (inv: "'a \<Rightarrow> bool")
end
