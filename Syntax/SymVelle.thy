theory SymVelle imports SymCelle
begin

record ('i, 'lix, 'ljx, 'ljix, 'lex, 'lcx, 'v) sym_velle = "('i, 'lix, 'ljx, 'ljix, 'lex, 'lcx) sym_celle" +
    var' :: "'v option"

record ('i, 'lix, 'ljx, 'ljix, 'lex, 'lcx, 'v, 'o) sym_velle_disc =
      "('i, 'lix, 'ljx, 'ljix, 'lex, 'lcx, 'o) sym_celle_disc" +
      var'd :: "'v \<Rightarrow> 'o"

definition sym_velle_emp :: "('i, 'lix, 'ljx, 'ljix, 'lex, 'lcx, 'v) sym_velle" where
 "sym_velle_emp = sym_celle.extend sym_celle_emp \<lparr> var' = None \<rparr>"

definition LVar :: "'v \<Rightarrow> ('i, 'lix, 'ljx, 'ljix, 'lex, 'lcx, 'v) sym_velle" where
 "LVar x = sym_velle.var'_update (\<lambda> _ . Some x) sym_velle_emp"
      
fun sym_velle_cases' ::
  "('i, 'lix, 'ljx, 'ljix, 'lex, 'lcx, 'v, 'x) sym_velle_scheme \<Rightarrow>
   ('i, 'lix, 'ljx, 'ljix, 'lex, 'lcx, 'v, 'o, 'xs) sym_velle_disc_scheme \<Rightarrow> 'o option" where
   "sym_velle_cases' s d =
      (case sym_celle_cases' s d of Some out \<Rightarrow> Some out
| _ \<Rightarrow> case var' s of Some x \<Rightarrow> Some (var'd d x)
| _ \<Rightarrow> None)"

fun sym_velle_fieldstatus :: "('i, 'lix, 'ljx, 'ljix, 'lex, 'lcx, 'v, 'x) sym_velle_scheme  \<Rightarrow> bool list" where
"sym_velle_fieldstatus i = sym_celle_fieldstatus i @ 
                      [is_some (var' i)]"
end