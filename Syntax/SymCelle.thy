theory SymCelle imports SymEmbelle
begin

(* Elle extended with calls *)
record ('i, 'lix, 'ljx, 'ljix, 'lex, 'lcx) sym_celle = "('i, 'lix, 'ljx, 'ljix, 'lex) sym_embelle" +
  lcall' :: "'lcx option"

record ('i, 'lix, 'ljx, 'ljix, 'lex, 'lcx, 'o) sym_celle_disc =
  "('i, 'lix, 'ljx, 'ljix, 'lex, 'o) sym_embelle_disc" +
    lcall'd :: "'lcx \<Rightarrow> 'o"

definition sym_celle_emp :: "('i, 'lix, 'ljx, 'ljix, 'lex, 'lcx) sym_celle" where
      "sym_celle_emp = sym_embelle.extend sym_embelle_emp \<lparr>lcall' = None \<rparr>"

definition LCall :: "'lcx \<Rightarrow> ('i, 'lix, 'ljx, 'ljix, 'lex, 'lcx) sym_celle" where
"LCall x = sym_celle.lcall'_update (\<lambda> _ . Some x) sym_celle_emp"
      
fun sym_celle_cases' ::
   "('i, 'lix, 'ljx, 'ljix, 'lex, 'lcx, 'x) sym_celle_scheme \<Rightarrow>
    ('i, 'lix, 'ljx, 'ljix, 'lex, 'lcx, 'o, 'xs) sym_celle_disc_scheme \<Rightarrow> 'o option" where
      "sym_celle_cases' s d =
        (case sym_embelle_cases' s d of Some out \<Rightarrow> Some out
| _ \<Rightarrow> case lcall' s of Some x \<Rightarrow> Some (lcall'd d x)
| _ \<Rightarrow> None)"

fun sym_celle_fieldstatus :: "('i, 'lix, 'ljx, 'ljix, 'lex, 'lcx, 'x) sym_celle_scheme  \<Rightarrow> bool list" where
"sym_celle_fieldstatus i = sym_embelle_fieldstatus i @ 
                      [is_some (lcall' i)]"

end