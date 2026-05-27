theory BacktrackArray_Types
  imports "NTP4Verif.NTP4Verif" "Functions_Config" "Functions_Func" "Predicates_Pred"
begin
datatype 'a timestamp = timestamp'mk (time: "int") (size: "int") (table: "int \<Rightarrow> 'a list")
datatype 'a t = t'mk (history: "int list") (current_time: "int") (buffer: "'a list list") (inv: "'a \<Rightarrow> bool")
end
