theory SymI imports "../SyntaxUtils"
begin
(* Syntax with instructions *)

record 'i sym_i =
  inst' :: "'i option"

record ('i, 'o) sym_i_disc =
  inst'd :: "'i \<Rightarrow> 'o"

  definition sym_i_emp :: "('i) sym_i" where
    "sym_i_emp = \<lparr> inst' = None\<rparr>"
    
fun sym_i_cases' ::
   "('i, 'x) sym_i_scheme \<Rightarrow> ('i, 'o, 'xs) sym_i_disc_scheme \<Rightarrow> 'o option" where
"sym_i_cases' s d =
  (case (inst' s) of 
         None \<Rightarrow> None
        | Some i \<Rightarrow> Some (inst'd d i))" 

definition LInst :: "'i \<Rightarrow> 'i sym_i" where
    "LInst x = \<lparr> inst' = Some x \<rparr>"

fun onetrue :: "bool list \<Rightarrow> bool" where
"onetrue l = 
    (case List.filter (\<lambda> b . b) l of
        [_] \<Rightarrow> True
        | _ \<Rightarrow> False)"

fun is_some :: "'o option \<Rightarrow> bool" where
"is_some None = False"
| "is_some _ = True"

fun sym_i_fieldstatus :: "('i, 'x) sym_i_scheme \<Rightarrow> bool list" where
"sym_i_fieldstatus i = [is_some (inst' i)]"

(* TODO: fun or def? use sym_i or sym_i_scheme? *)
fun sym_i_notamb :: "'i sym_i \<Rightarrow> bool" where
  "sym_i_notamb i =
    onetrue (sym_i_fieldstatus i)"
    
end