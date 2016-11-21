theory L1_examples
  imports L1
begin

schematic_goal ex2: "((l(0) := #7); (l(1) := (!l(0) .+. #2)), [0 \<mapsto> 0, 1 \<mapsto> 1]) \<Rightarrow>\<^sup>* ?t"
 by force

schematic_goal slide22_auto: "(
  l(2) := #0;
  while !l(1) .\<ge>. #1 do (
    l(2) := (!l(2) .+. !l(1));
    l(1) := (!l(1) .+. #(-1))
  ) od
  , [1 \<mapsto> 3, 2 \<mapsto> 0]) \<Rightarrow>\<^sup>* ?t"
by force

schematic_goal "[0 \<mapsto> Numref] \<turnstile> (while !l(0) .\<ge>. #2 do l(0) := (!l(0) .+. #1); skip od) : ?T"
  by force
end