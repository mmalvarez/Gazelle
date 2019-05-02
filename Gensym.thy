theory Gensym imports Main
begin

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


end