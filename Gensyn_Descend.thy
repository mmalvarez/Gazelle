theory Gensyn_Descend imports Gensyn
begin

type_synonym childpath = "nat list"

inductive gensyn_descend ::
  "('b, 'r, 'g) gensyn \<Rightarrow> 
   ('b, 'r, 'g) gensyn \<Rightarrow>
   childpath \<Rightarrow> bool
  "
  where
  " \<And> c ls t g r .
    c < length ls \<Longrightarrow>
    List.nth ls c = t \<Longrightarrow>
    gensyn_descend (GRec g r ls) t [c]"
| "\<And> t t' l t'' l' .
      gensyn_descend t t' l \<Longrightarrow>
      gensyn_descend t' t'' l' \<Longrightarrow>
      gensyn_descend t t'' (l@l')"

(* gensyn_get, functional version of gensyn_descend
both versions are useful in different places *)
fun gensyn_get :: "('b, 'r, 'g) gensyn \<Rightarrow> childpath \<Rightarrow> ('b, 'r, 'g) gensyn option" and
gensyn_get_list :: "('b, 'r, 'g) gensyn list \<Rightarrow> childpath \<Rightarrow> ('b, 'r, 'g) gensyn option" where
    "gensyn_get T [] = Some T"
  | "gensyn_get (GRec g r ls) p = 
     gensyn_get_list ls p"
  | "gensyn_get _ _ = None"

| "gensyn_get_list _ [] = None" (* this should never happen *)
| "gensyn_get_list [] _ = None" (* this case will happen when we cannot find a node *)
| "gensyn_get_list (h#ls) (0#p) = gensyn_get h p"
| "gensyn_get_list (_#ls) (n#p) = 
   gensyn_get_list (ls) ((n-1)#p)"

(* Tool for getting the next valid child in the tree *)
fun gensyn_cp_next :: "('b, 'r, 'g) gensyn \<Rightarrow> childpath \<Rightarrow> childpath option"
and gensyn_cp_next_list :: "('b, 'r, 'g) gensyn list \<Rightarrow> childpath \<Rightarrow> childpath option" 
where
"gensyn_cp_next (GRec _ _ l) (cp) = gensyn_cp_next_list l cp"
| "gensyn_cp_next _ _ = None"

| "gensyn_cp_next_list [] _ = None"
| "gensyn_cp_next_list _ [] = None" (* corresponds to hitting a list case with no cp left - we want to go to its sibling*)
(* idea: maintain a lookahead of 1. this is why we talk about both cases *)
(* do we need to be tacking on a 0 *)
| "gensyn_cp_next_list ([h]) (0#cpt) =
    (case gensyn_cp_next h cpt of None \<Rightarrow> None 
                         | Some res \<Rightarrow> Some (0#res))"
| "gensyn_cp_next_list ([h]) ((Suc n)#cpt) = None"
| "gensyn_cp_next_list (h1#h2#t) (0#cpt) =
    (case gensyn_cp_next h1 cpt of
      Some cp' \<Rightarrow> Some (0#cp')
     | None \<Rightarrow> Some [1])"
| "gensyn_cp_next_list (h#h2#t) (Suc n # cpt) =
    (case gensyn_cp_next_list (h2#t) (n # cpt) of
      Some (n'#cp') \<Rightarrow> Some (Suc n' # cp')
     | _ \<Rightarrow> None)
    "

fun gensyn_cp_next' :: "('b, 'r, 'g) gensyn \<Rightarrow> childpath \<Rightarrow> childpath option"
  where
"gensyn_cp_next' g cp =
  (case (rev cp) of
      [] \<Rightarrow> None
    | (cl # cp') \<Rightarrow>
        (case (gensyn_get g (rev cp')) of
              Some (GRec _ _ l) \<Rightarrow>
                (if cl + 1 < length l then Some (rev ((cl + 1)#cp'))
                 else gensyn_cp_next' g (rev cp'))
            | Some (GBase _ _) \<Rightarrow> None
            | None \<Rightarrow> None))"

(* idea: this will attempt to go to the next immediate child of our node
   if it is a list node *)
(* TODO: should we define this recursively like cp_next *)
fun gensyn_dig :: "('b, 'r, 'g) gensyn \<Rightarrow> childpath \<Rightarrow> childpath option" where
"gensyn_dig g c =
  (case gensyn_get g c of
    Some (GRec _ _ (h#t)) \<Rightarrow> Some (c@[0])
    | _ \<Rightarrow> None)"

(* another option for defining cp_next. this should work for our purposes as well *)
(*
fun gensyn_cp_next2' :: "('b, 'r, 'g) gensyn \<Rightarrow> childpath \<Rightarrow> childpath option" where
"gensyn_cp_next2' g cp =
  (case gensyn_get g cp of
    
  

  (case (rev cp) of
      [] \<Rightarrow> None
    | (cl # cp') \<Rightarrow>
        (case (gensyn_get g (rev cp')) of
              Some (GRec _ _ l) \<Rightarrow>
                (if cl + 1 < length l then Some (rev ((cl + 1)#cp'))
                 else gensyn_cp_next' g (rev cp'))
            | _ \<Rightarrow> None))"
*)
end 
