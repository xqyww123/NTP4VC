theory bellman_ford_Graph_vertices_cardinal_posqtvc
  imports "NTP4Verif.NTP4Verif"
begin
typedecl  vertex
consts vertices :: "vertex fset"
consts edges :: "(vertex \<times> vertex) fset"
definition edge :: "vertex \<Rightarrow> vertex \<Rightarrow> _"
  where "edge x y \<longleftrightarrow> (x, y) |\<in>| edges" for x y
axiomatization where edges_def'0:   "x |\<in>| vertices"
 if "(x, y) |\<in>| edges"
  for x :: "vertex"
  and y :: "vertex"
axiomatization where edges_def'1:   "y |\<in>| vertices"
 if "(x, y) |\<in>| edges"
  for x :: "vertex"
  and y :: "vertex"
consts s :: "vertex"
axiomatization where s_def:   "s |\<in>| vertices"
theorem vertices_cardinal_pos'vc:
  shows "(0 :: int) < int (fcard vertices)"
  sorry
end
