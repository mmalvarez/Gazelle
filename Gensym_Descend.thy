theory Gensym_Descend imports Gensym
begin

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

(* gensym_get, functional version of gensym_descend
both versions are useful in different places *)
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

(* Tool for getting the next valid child in the tree *)
fun gensym_cp_next :: "('b, 'r, 'g) gensym \<Rightarrow> childpath \<Rightarrow> childpath option"
and gensym_cp_next_list :: "('b, 'r, 'g) gensym list \<Rightarrow> childpath \<Rightarrow> childpath option" 
where
"gensym_cp_next (GRec _ _ l) (cp) = gensym_cp_next_list l cp"
| "gensym_cp_next _ _ = None"

| "gensym_cp_next_list [] _ = None"
| "gensym_cp_next_list _ [] = None" (* corresponds to hitting a list case with no cp left - we want to go to its sibling*)
(* idea: maintain a lookahead of 1. this is why we talk about both cases *)
(* do we need to be tacking on a 0 *)
| "gensym_cp_next_list ([h]) (0#cpt) =
    (case gensym_cp_next h cpt of None \<Rightarrow> None 
                         | Some res \<Rightarrow> Some (0#res))"
| "gensym_cp_next_list ([h]) ((Suc n)#cpt) = None"
| "gensym_cp_next_list (h1#h2#t) (0#cpt) =
    (case gensym_cp_next h1 cpt of
      Some cp' \<Rightarrow> Some (0#cp')
     | None \<Rightarrow> Some [1])"
| "gensym_cp_next_list (h#h2#t) (Suc n # cpt) =
    (case gensym_cp_next_list (h2#t) (n # cpt) of
      Some (n'#cp') \<Rightarrow> Some (Suc n' # cp')
     | _ \<Rightarrow> None)
    "

fun gensym_cp_next' :: "('b, 'r, 'g) gensym \<Rightarrow> childpath \<Rightarrow> childpath option"
  where
"gensym_cp_next' g cp =
  (case (rev cp) of
      [] \<Rightarrow> None
    | (cl # cp') \<Rightarrow>
        (case (gensym_get g (rev cp')) of
              Some (GRec _ _ l) \<Rightarrow>
                (if cl + 1 < length l then Some (rev ((cl + 1)#cp'))
                 else gensym_cp_next' g (rev cp'))
            | Some (GBase _ _) \<Rightarrow> None
            | None \<Rightarrow> None))"

(* idea: this will attempt to go to the next immediate child of our node
   if it is a list node *)
(* TODO: should we define this recursively like cp_next *)
fun gensym_dig :: "('b, 'r, 'g) gensym \<Rightarrow> childpath \<Rightarrow> childpath option" where
"gensym_dig g c =
  (case gensym_get g c of
    Some (GRec _ _ (h#t)) \<Rightarrow> Some (c@[0])
    | _ \<Rightarrow> None)"

(* another option for defining cp_next. this should work for our purposes as well *)
(*
fun gensym_cp_next2' :: "('b, 'r, 'g) gensym \<Rightarrow> childpath \<Rightarrow> childpath option" where
"gensym_cp_next2' g cp =
  (case gensym_get g cp of
    
  

  (case (rev cp) of
      [] \<Rightarrow> None
    | (cl # cp') \<Rightarrow>
        (case (gensym_get g (rev cp')) of
              Some (GRec _ _ l) \<Rightarrow>
                (if cl + 1 < length l then Some (rev ((cl + 1)#cp'))
                 else gensym_cp_next' g (rev cp'))
            | _ \<Rightarrow> None))"
*)
end 
