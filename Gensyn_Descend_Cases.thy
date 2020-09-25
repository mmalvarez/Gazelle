theory Gensyn_Descend imports Gensyn
begin

type_synonym childpath = "nat list"

inductive gensyn_descend ::
  "('x) gensyn \<Rightarrow> 
   ('x) gensyn \<Rightarrow>
   childpath \<Rightarrow> bool
  "
  where
  " \<And> c ls t x .
    c < length ls \<Longrightarrow>
    List.nth ls c = t \<Longrightarrow>
    gensyn_descend (G x ls) t [c]"
| "\<And> t t' l t'' l' .
      gensyn_descend t t' l \<Longrightarrow>
      gensyn_descend t' t'' l' \<Longrightarrow>
      gensyn_descend t t'' (l@l')"

(* gensyn_get, functional version of gensyn_descend
both versions are useful in different places *)

fun gensyn_get_list :: "'x gensyn list \<Rightarrow> childpath \<Rightarrow> 'x gensyn option" where
"gensyn_get_list l cp = 
  (case l of
       [] \<Rightarrow> None
       | ((G x ld)#lt) \<Rightarrow> (case cp of
          [0] \<Rightarrow> Some (G x ld)
          | (0#ct) \<Rightarrow> gensyn_get_list ld ct
          | (n#ct) \<Rightarrow> gensyn_get_list lt ((n-1)#ct)))"


(*
fun gensyn_get :: "('x) gensyn \<Rightarrow> childpath \<Rightarrow> ('x) gensyn option" and
gensyn_get_list :: "('x) gensyn list \<Rightarrow> childpath \<Rightarrow> ('x) gensyn option"  where
    "gensyn_get T [] = Some T"
  | "gensyn_get (G x ls) p = 
     gensyn_get_list ls p"

| "gensyn_get_list _ [] = None" (* this should never happen *)
| "gensyn_get_list [] _ = None" (* this case will happen when we cannot find a node *)
| "gensyn_get_list (h#ls) (0#p) = gensyn_get h p"
| "gensyn_get_list (_#ls) (n#p) = 
   gensyn_get_list (ls) ((n-1)#p)"
*)

fun gensyn_get :: "('x) gensyn \<Rightarrow> childpath \<Rightarrow> ('x) gensyn option" where
"gensyn_get T p = 
  (case p of [] \<Rightarrow> Some T
   | _ \<Rightarrow> (case T of (G _ l) \<Rightarrow> gensyn_get_list l p))"

fun gensyn_cp_next_list :: "('x) gensyn list \<Rightarrow> childpath \<Rightarrow> childpath option"  where
"gensyn_cp_next_list l cp =
  (case l of
    [] \<Rightarrow> None
    | [(G x l)] \<Rightarrow> 
      (case cp of
        [] \<Rightarrow> None
        | (0#cpt) \<Rightarrow> (case gensyn_cp_next_list l cpt of None \<Rightarrow> None 
                         | Some res \<Rightarrow> Some (0#res))
        | (Suc n)#cpt \<Rightarrow> None)
    | (G x l)#h2#t \<Rightarrow>
      (case cp of
        [] \<Rightarrow> None
        | (0#cpt) \<Rightarrow> (case gensyn_cp_next_list l cpt of None \<Rightarrow> Some [1]
                       | Some cp' \<Rightarrow> Some (0#cp'))
        | (Suc n)#cpt \<Rightarrow> (case gensyn_cp_next_list (h2#t) (n # cpt) of None \<Rightarrow> None
                       | Some [] \<Rightarrow> None     
                       | Some (n'#cp') \<Rightarrow> Some (Suc n' # cp'))))"


(* Tool for getting the next valid child in the tree *)
fun gensyn_cp_next :: "('x) gensyn \<Rightarrow> childpath \<Rightarrow> childpath option"
  where
"gensyn_cp_next (G _ l) (cp) = gensyn_cp_next_list l cp"

(* this may no longer be useful. *)
fun gensyn_cp_next' :: "('x) gensyn \<Rightarrow> childpath \<Rightarrow> childpath option"
  where
"gensyn_cp_next' g cp =
  (case (rev cp) of
      [] \<Rightarrow> None
    | (cl # cp') \<Rightarrow>
        (case (gensyn_get g (rev cp')) of
              Some (G _ l) \<Rightarrow>
                (if cl + 1 < length l then Some (rev ((cl + 1)#cp'))
                 else gensyn_cp_next' g (rev cp'))
            | None \<Rightarrow> None))"

(* idea: this will attempt to go to the next immediate child of our node
   if it is a list node *)
(* TODO: should we define this recursively like cp_next *)
fun gensyn_dig :: "('x) gensyn \<Rightarrow> childpath \<Rightarrow> childpath option" where
"gensyn_dig g c =
  (case gensyn_get g c of
    Some (G _ (h#t)) \<Rightarrow> Some (c@[0])
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
