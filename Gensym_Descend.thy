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
end
