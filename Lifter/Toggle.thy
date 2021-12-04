theory Toggle
  imports Lifter
begin
(*
idea: based on the syntax, we can decide to do a no-op
otherwise we have to obey normal lifting rules.
*)

definition LtUpd ::
  "('syn, 'a, 'b) lifting \<Rightarrow>
   ('syn \<Rightarrow> bool) \<Rightarrow>
   'syn \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" where
"LtUpd l tg syn a b =
  (if tg syn then LUpd l syn a b
   else b)"
  
  

end