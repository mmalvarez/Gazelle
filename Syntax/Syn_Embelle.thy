theory Syn_Embelle imports Main "../Syntax_Utils"
begin
(* TODO: Elle extended with arbitrary embedded content
   idea: semantics need to be proven to never reach this content *)

type_synonym  ('lex, 'xb, 'xa) syn_embelle =
  "'xb + 'lex + 'xa"

type_synonym ('lex, 'xb, 'xa, 'lexo) syn_embelle_disc =
  "('xb * ('lex \<Rightarrow> 'lexo) * 'xa)"

      
definition LEmbed :: "'lex \<Rightarrow> ('lex, 'xa, 'xb) syn_embelle" where
"LEmbed x = snth2h x"

end