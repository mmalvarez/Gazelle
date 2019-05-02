theory Syntax imports Main
begin

(* need to refactor this. ideal flow:
this file is deprecated.
- Gensym
\<rightarrow> Syntaxes/sym_i
\<rightarrow> syntaxes/sym_elle 
\<rightarrow> embelle
-> celle
-> velle
*)

datatype ('b, 'r, 'g) gensym = 
  GBase "'g" "'b"
  | GRec "'g" "'r" "(('b, 'r, 'g) gensym) list"

(* TODO: induction principle for gensym *)
(* are we using g and r correctly? *)
lemma gensym_induct:
  assumes Lb: "(\<And> (g :: 'g) (b :: 'b) . P1 (GBase g b))"
  and Lr : "(\<And> g r l . P2 l \<Longrightarrow> P1 (GRec g r l))"
  and Lrn : "\<And> g r . P2 []"
  and Lrc : "\<And>t g r l . P1 t \<Longrightarrow>
                         P2 l \<Longrightarrow> 
                         P2 (t # l)"
  shows "P1 t \<and> P2 l"
proof-
  {fix t
    have "P1 t \<and> (\<forall> g r l . t = GRec g r l \<longrightarrow> P2 l)"
    proof (induction)
    case (GBase g b) thus ?case using Lb by auto next
    case (GRec g r l) thus ?case
    apply (induct l) using Lr Lrn Lrc
    apply(auto) apply(force) apply(force)
    done
    qed}
  
  thus ?thesis by auto
  qed

type_synonym childpath = "nat list"

inductive gensym_descend ::
  "('b, 'r, 'g) gensym \<Rightarrow> 
   ('b, 'r, 'g) gensym \<Rightarrow>
   childpath \<Rightarrow> bool
  "
  where
  " \<And> c ls t g r .
    c < length ls \<Longrightarrow>
    List.nth ls c = t \<Longrightarrow>
    gensym_descend (GRec g r ls) t [c]"
| "\<And> t t' l t'' l' .
      gensym_descend t t' l \<Longrightarrow>
      gensym_descend t' t'' l' \<Longrightarrow>
      gensym_descend t t'' (l@l')"

(* gensym_get *)
fun gensym_get :: "('b, 'r, 'g) gensym \<Rightarrow> childpath \<Rightarrow> ('b, 'r, 'g) gensym option" and
gensym_get_list :: "('b, 'r, 'g) gensym list \<Rightarrow> childpath \<Rightarrow> ('b, 'r, 'g) gensym option" where
    "gensym_get T [] = Some T"
  | "gensym_get (GRec g r ls) p = 
     gensym_get_list ls p"
  | "gensym_get _ _ = None"

| "gensym_get_list _ [] = None" (* this should never happen *)
| "gensym_get_list [] _ = None" (* this case will happen when we cannot find a node *)
| "gensym_get_list (h#ls) (0#p) = gensym_get h p"
| "gensym_get_list (_#ls) (n#p) = 
   gensym_get_list (ls) ((n-1)#p)"

(* Define LSeq here? *)

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
        
(* Elle syntax *)
    
record ('i, 'lix, 'ljx, 'ljix) sym_elle = "'i sym_i" +
  llab' :: "'lix option"
  ljmp' :: "'ljx option"
  ljmpi' :: "'ljix option"

  definition sym_elle_emp :: "('i, 'lix, 'ljx, 'ljix) sym_elle" where
  "sym_elle_emp = sym_i.extend sym_i_emp \<lparr> llab' = None, ljmp' = None, ljmpi' = None \<rparr>"
  
  record ('i, 'lix, 'ljx, 'ljix, 'o) sym_elle_disc =
    "('i, 'o) sym_i_disc" +
      llab'd :: "'lix \<Rightarrow> 'o"
      ljmp'd :: "'ljx \<Rightarrow> 'o"
      ljmpi'd :: "'ljix \<Rightarrow> 'o"

  (* TODO: want to have cases for just the new things? *)
  fun sym_elle_cases' ::
  "('i, 'lix, 'ljx, 'ljix, 'x) sym_elle_scheme \<Rightarrow>
   ('i, 'lix, 'ljx, 'ljix, 'o, 'xs) sym_elle_disc_scheme \<Rightarrow> 'o option" where
   "sym_elle_cases' s d =
      (case sym_i_cases' s d of Some out \<Rightarrow> Some out
| _ \<Rightarrow> case llab' s of Some x \<Rightarrow> Some (llab'd d x)
| _ \<Rightarrow> case ljmp' s of Some x \<Rightarrow> Some (ljmp'd d x)
|_ \<Rightarrow>  case ljmpi' s of Some x \<Rightarrow> Some (ljmpi'd d x))"

definition LLab :: "'lix \<Rightarrow> ('i, 'lix, 'ljx, 'ljix) sym_elle" where
"LLab x = sym_elle.llab'_update (\<lambda> _ . Some x) sym_elle_emp"

definition LJmp :: "'ljx \<Rightarrow> ('i, 'lix, 'ljx, 'ljix) sym_elle" where
"LJmp x = sym_elle.ljmp'_update (\<lambda> _ . Some x) sym_elle_emp"

definition LJmpI :: "'ljix \<Rightarrow> ('i, 'lix, 'ljx, 'ljix) sym_elle" where
"LJmpI x = sym_elle.ljmpi'_update (\<lambda> _ . Some x) sym_elle_emp"

fun sym_elle_fieldstatus :: "('i, 'lix, 'ljx, 'ljix, 'x) sym_elle_scheme  \<Rightarrow> bool list" where
"sym_elle_fieldstatus i = sym_i_fieldstatus i @ 
                      [is_some (llab' i)
                      ,is_some (ljmp' i)
                      ,is_some (ljmpi' i)]"

(* TODO: more notambs? *)
(* fun sym_elle_notamb :: ... *)

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

(* utility functions for making these look like
   normal case analyses *)

fun oforce :: "'o option \<Rightarrow> 'o" where
"oforce (Some out) = out"
| "oforce None = undefined"



  end