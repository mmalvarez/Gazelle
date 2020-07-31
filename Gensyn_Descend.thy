theory Gensyn_Descend imports Gensyn
begin


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
fun gensyn_get_list :: "('x) gensyn list \<Rightarrow> childpath \<Rightarrow> ('x) gensyn option"  where
 "gensyn_get_list [] _ = None" (* this case will happen when we cannot find a node *)
| "gensyn_get_list _ [] = None"
| "gensyn_get_list ((h)#lt) ([0]) = Some h"
| "gensyn_get_list ((G x ld)#lt) (0#ct) = gensyn_get_list ld ct"
| "gensyn_get_list (_#ls) (n#p) = 
   gensyn_get_list (ls) ((n-1)#p)"

fun gensyn_get :: "('x) gensyn \<Rightarrow> childpath \<Rightarrow> ('x) gensyn option" where
"gensyn_get T [] = Some T"
| "gensyn_get (G x ls) p = gensyn_get_list ls p"

(* Tool for getting the next valid child in the tree *)
fun gensyn_cp_next_list :: "('x) gensyn list \<Rightarrow> childpath \<Rightarrow> childpath option" 
  where
  "gensyn_cp_next_list [] _ = None"
| "gensyn_cp_next_list _ [] = None"
| "gensyn_cp_next_list ([G x l]) (0#cpt) =
    (case gensyn_cp_next_list l cpt of None \<Rightarrow> None 
                         | Some res \<Rightarrow> Some (0#res))"
| "gensyn_cp_next_list ([h]) ((Suc n)#cpt) = None"
| "gensyn_cp_next_list ((G x l)#h2#t) (0#cpt) =
    (case gensyn_cp_next_list l cpt of
      Some cp' \<Rightarrow> Some (0#cp')
     | None \<Rightarrow> Some [1])"
| "gensyn_cp_next_list (h#h2#t) (Suc n # cpt) =
    (case gensyn_cp_next_list (h2#t) (n # cpt) of
      Some (n'#cp') \<Rightarrow> Some (Suc n' # cp')
     | _ \<Rightarrow> None)"

fun gensyn_cp_next :: "('x) gensyn \<Rightarrow> childpath \<Rightarrow> childpath option"
  where
"gensyn_cp_next (G x l) (cp) = gensyn_cp_next_list l cp"

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

definition gs_ex :: "unit gensyn" where
"gs_ex =
  G () [G () [], G () [G () [], G () []], G () []]"

value "gensyn_cp_next gs_ex [1, 1]"

(*
fun gensyn_cp_sibling_list :: "'x gensyn list \<Rightarrow> childpath \<Rightarrow> childpath option" where
  "gensyn_cp_sibling_list [] _ = None"
| "gensyn_cp_sibling_list (h#t) [] = Some []"
| "gensyn_cp_sibling_list ([G x l]) (0#cpt) =
    (case gensyn_cp_sibling_list l cpt of None \<Rightarrow> None 
                         | Some res \<Rightarrow> Some (0#res))"
| "gensyn_cp_sibling_list ([h]) ((Suc n)#cpt) = None"
| "gensyn_cp_sibling_list ((G x l)#h2#t) (0#cpt) =
    (case gensyn_cp_sibling_list l cpt of
      Some cp' \<Rightarrow> Some (0#cp')
     | None \<Rightarrow> None)"
| "gensyn_cp_sibling_list (h#h2#t) (Suc n # cpt) =
    (case gensyn_cp_sibling_list (h2#t) (n # cpt) of
      Some (n'#cp') \<Rightarrow> Some (Suc n' # cp')
     | _ \<Rightarrow> None)"
*)

fun gensyn_cp_sibling_list_ht :: "'x gensyn list \<Rightarrow> nat \<Rightarrow> childpath \<Rightarrow> (nat * childpath) option" where
  "gensyn_cp_sibling_list_ht [] _ _ = None"
| "gensyn_cp_sibling_list_ht [h] _ [] = None"
| "gensyn_cp_sibling_list_ht [h] (Suc n) _ = None"

| "gensyn_cp_sibling_list_ht (h1#h2#t) 0 [] = Some (1, [])"
| "gensyn_cp_sibling_list_ht ((G x l)#t) 0 (ch#ct) = 
    (case gensyn_cp_sibling_list_ht l ch ct of
      Some (n', cp') \<Rightarrow> Some (0, n'#cp')
      | _ \<Rightarrow> None)"


| "gensyn_cp_sibling_list_ht ((G x l)#h2#t) (Suc n) ct =
    (case gensyn_cp_sibling_list_ht (h2#t) n (ct) of
      Some (n', cp') \<Rightarrow> Some (Suc n', cp')
     | _ \<Rightarrow> None)"


fun gensyn_cp_sibling :: "('x) gensyn \<Rightarrow> childpath \<Rightarrow> childpath option"
  where
"gensyn_cp_sibling (G x l) [] = None"
| "gensyn_cp_sibling (G x l) (ch#ct) =
    (case gensyn_cp_sibling_list_ht l ch ct of
      None \<Rightarrow> None
      | Some (ch', ct') \<Rightarrow> Some (ch'#ct'))"

value "gensyn_cp_sibling gs_ex [1]"
value "gensyn_cp_sibling_list
([G () [], G () [], G () []])
[0]"

fun gensyn_cp_parent :: "'x gensyn \<Rightarrow> childpath \<Rightarrow> childpath option" where
"gensyn_cp_parent _ [] = None"
| "gensyn_cp_parent g (h#t) = Some (butlast (h#t))"

(* is the second argument an extension of the first? *)
fun gensyn_cp_is_desc :: "childpath \<Rightarrow> childpath \<Rightarrow> bool" where
"gensyn_cp_is_desc [] cp = True"
| "gensyn_cp_is_desc (h1#t1) [] = False"
| "gensyn_cp_is_desc (h1#t1) (h2#t2) =
    (h1 = h2 \<and> gensyn_cp_is_desc t1 t2)"

fun gensyn_cp_is_desc_strict :: "childpath \<Rightarrow> childpath \<Rightarrow> bool" where
"gensyn_cp_is_desc_strict cp [] = False" 
| "gensyn_cp_is_desc_strict [] (h2#t2) = True"
| "gensyn_cp_is_desc_strict (h1#t1) (h2#t2) =
    (h1 = h2 \<and> gensyn_cp_is_desc_strict t1 t2)"

fun get_suffix :: "childpath \<Rightarrow> childpath \<Rightarrow> childpath option" where
"get_suffix cp [] = None"
| "get_suffix [] (h2#t2) = Some (h2#t2)"
| "get_suffix (h1#t1) (h2#t2) =
  (if h1 = h2 then get_suffix t1 t2 else None)"


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
