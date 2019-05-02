theory SymEmbelle imports SymElle
begin
(* TODO: Elle extended with arbitrary embedded content
   idea: semantics need to be proven to never reach this content *)

   record ('i, 'lix, 'ljx, 'ljix, 'lex) sym_embelle =
    "('i, 'lix, 'ljx, 'ljix) sym_elle" +
        lembed' :: "'lex option"

definition sym_embelle_emp :: "('i, 'lix, 'ljx, 'ljix, 'lex) sym_embelle" where
  "sym_embelle_emp = sym_elle.extend sym_elle_emp \<lparr> lembed' = None \<rparr>"

  record ('i, 'lix, 'ljx, 'ljix, 'lex, 'o) sym_embelle_disc =
    "('i, 'lix, 'ljx, 'ljix, 'o) sym_elle_disc" +
      lembed'd :: "'lex \<Rightarrow> 'o"
      
definition LEmbed :: "'lex \<Rightarrow> ('i, 'lix, 'ljx, 'ljix, 'lex) sym_embelle" where
    "LEmbed x = sym_embelle.lembed'_update (\<lambda> _ . Some x) sym_embelle_emp"

fun sym_embelle_cases' ::
   "('i, 'lix, 'ljx, 'ljix, 'lex, 'x) sym_embelle_scheme \<Rightarrow>
    ('i, 'lix, 'ljx, 'ljix, 'lex, 'o, 'xs) sym_embelle_disc_scheme \<Rightarrow> 'o option" where
      "sym_embelle_cases' s d =
        (case sym_elle_cases' s d of Some out \<Rightarrow> Some out
| _ \<Rightarrow> case lembed' s of Some x \<Rightarrow> Some (lembed'd d x)
| _ \<Rightarrow> None)"

fun sym_embelle_fieldstatus :: "('i, 'lix, 'ljx, 'ljix, 'lex, 'x) sym_embelle_scheme  \<Rightarrow> bool list" where
"sym_embelle_fieldstatus i = sym_elle_fieldstatus i @ 
                      [is_some (lembed' i)]"

end