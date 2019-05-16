theory Syntax_Utils imports Main
begin

(* general utilities for use in our extensible
syntax (see Syntaxes/ directory) *)

(* used for validity checks to ensure only
one node type is selected *)
fun onetrue :: "bool list \<Rightarrow> bool" where
"onetrue l = 
    (case List.filter (\<lambda> b . b) l of
        [_] \<Rightarrow> True
        | _ \<Rightarrow> False)"

fun is_some :: "'o option \<Rightarrow> bool" where
"is_some None = False"
| "is_some _ = True"

(* used to make discriminators look more like
   normal functions (for valid syntax nodes,
   undefined should never be reached) *)
fun oforce :: "'o option \<Rightarrow> 'o" where
"oforce (Some out) = out"
| "oforce None = undefined"

end