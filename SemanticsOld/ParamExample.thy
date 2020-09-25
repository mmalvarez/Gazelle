theory ParamExample imports Main

begin

(* generic syntax *)
datatype ('b, 'r, 'g) gensyn = 
  GBase "'g" "'b"
  | GRec "'g" "'r" "(('b, 'r, 'g) gensyn) list"

(* we define a more useful induction principle, omitted... *)

(* navigation within syntax trees. no need to worry too much about the details of this;
   the type is what matters most *)
type_synonym childpath = "nat list"
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


(* result type for use with semantics *)
datatype gs_result =
  GRUnhandled
  | GRPath childpath
  | GRCrash
  | GRDone

fun gensyn_numnodes :: "('a, 'b, 'c) gensyn \<Rightarrow> nat" and
    gensyn_numnodes_l :: "('a, 'b, 'c) gensyn list \<Rightarrow> nat" where
"gensyn_numnodes (GBase _ _) = 1"
| "gensyn_numnodes (GRec _ _ l) = 1 + gensyn_numnodes_l l"
| "gensyn_numnodes_l [] = 1"
| "gensyn_numnodes_l (h#t) = gensyn_numnodes h + gensyn_numnodes_l t"

lemma gensyn_numnodes_l_nz : "gensyn_numnodes_l l > (0 :: nat)"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case 
    apply(case_tac a, auto)
    done
qed
(* another idea - define a function outside the locale to serve as an iterator *)
function gensyn_iterate' :: "(childpath \<Rightarrow> 'result) \<Rightarrow>
                        (childpath \<Rightarrow> 'result list \<Rightarrow> 'result) \<Rightarrow>
                        ('a, 'b, 'c) gensyn \<Rightarrow>                        
                        childpath \<Rightarrow>
                        'result" and
  gensyn_iterate'_l :: "(childpath \<Rightarrow> 'result) \<Rightarrow>
                        (childpath \<Rightarrow> 'result list \<Rightarrow> 'result) \<Rightarrow>
                        ('a, 'b, 'c) gensyn \<Rightarrow>
                        ('a, 'b, 'c) gensyn list \<Rightarrow>
                        nat \<Rightarrow>
                        childpath \<Rightarrow>
                        'result list" where
"gensyn_iterate' r f (GBase _ _) cp = r (rev cp)"
| "gensyn_iterate' r f (GRec _ _ []) cp = 
    f (rev cp) ([])"
| "gensyn_iterate' r f (GRec _ _ (lh#lt)) cp = 
    f (rev cp) (gensyn_iterate'_l r f lh lt 0 cp)"
| "gensyn_iterate'_l r f lh [] cph cp = 
    [gensyn_iterate' r f lh (cph#cp)]"
| "gensyn_iterate'_l r f lh (lh2#lt) cph cp =
   (gensyn_iterate' r f lh (cph#cp))#
   (gensyn_iterate'_l r f lh2 lt (cph+1) cp)"
  by pat_completeness auto
termination
  apply(relation 
      "measure (\<lambda> d . case d of
          (Inl (_, _, g, _)) \<Rightarrow> gensyn_numnodes g
          | (Inr (_, _, g, l, _, _)) \<Rightarrow> gensyn_numnodes g + gensyn_numnodes_l l)")
      apply(auto)
   apply(cut_tac l = lt in gensyn_numnodes_l_nz) apply(auto)
  apply(case_tac lh, auto)
  done

fun gensyn_iterate :: "(childpath \<Rightarrow> 'result) \<Rightarrow>
                        (childpath \<Rightarrow> 'result list \<Rightarrow> 'result) \<Rightarrow>
                        ('a, 'b, 'c) gensyn \<Rightarrow> 'result" where
"gensyn_iterate r f g = gensyn_iterate' r f g []"

fun firstSome :: "'a option list \<Rightarrow> 'a option" where
"firstSome [] = None"
| "firstSome (Some h # _) = Some h"
| "firstSome (None # t) = firstSome t"

(* is this enough to define e.g. "next"? *)
definition gensyn_dig :: "('a, 'b, 'c) gensyn \<Rightarrow> childpath \<Rightarrow> childpath option" where
"gensyn_dig t cp =
  gensyn_iterate
    (\<lambda> _ . None)
    (\<lambda> cp' l . (if cp = cp' then 
                   (if l = [] then None else Some (cp@[0]))
                else firstSome l)) t
  "

definition test_case1 :: "(unit, unit, unit) gensyn" where
"test_case1 =
  GRec () () [GRec () () [(GBase () ())], GBase () ()]"

(* ok, i buy it. let's see now *)

(* naive use of locale - inductive definition it contains doesn't typecheck *)
locale Semantics =
    fixes base_sem :: "'g \<Rightarrow> 
                      'b \<Rightarrow>
                      'mstate \<Rightarrow> 
                      'mstate \<Rightarrow> 
                      childpath \<Rightarrow>
                      (childpath \<Rightarrow> gs_result) \<Rightarrow>
                      (childpath \<Rightarrow> gs_result list \<Rightarrow> gs_result) \<Rightarrow>
                      bool"

  fixes rec_sem :: "'g \<Rightarrow>
                    'r \<Rightarrow>
                    'mstate \<Rightarrow>
                    'mstate \<Rightarrow>
                    childpath \<Rightarrow>
                    (childpath \<Rightarrow> gs_result) \<Rightarrow>
                    (childpath \<Rightarrow> gs_result list \<Rightarrow> gs_result) \<Rightarrow>
                    bool"

begin

(* this doesn't typecheck because "base_sem" and "rec_sem" are not treated as
   "let-polymorphic" constants *)
inductive gensyn_sem ::
  "('b, 'r, 'g) gensyn \<Rightarrow>
   childpath \<Rightarrow>
   'mstate \<Rightarrow>
   'mstate \<Rightarrow>
   bool
  "
  where
  "\<And> t cp g b fb fl m m' .
    gensyn_get t cp = Some (GBase g b) \<Longrightarrow>
    base_sem g b m m' cp fb fl \<Longrightarrow>
    gensyn_iterate fb fl t = GRDone \<Longrightarrow>
    gensyn_sem t cp m m'"

| "\<And> t cp g b fb fl m cp' m' m'' .
    gensyn_get t cp = Some (GBase g b) \<Longrightarrow>
    base_sem g b m m' cp fb fl \<Longrightarrow>
    gensyn_iterate fb fl t = GRPath cp' \<Longrightarrow>
    gensyn_sem t cp' m' m'' \<Longrightarrow>
    gensyn_sem t cp m m''"

| "\<And> t cp g r fb fl l m m' .
   gensyn_get t cp = Some (GRec g r l) \<Longrightarrow>
   rec_sem g r m m' cp fb fl \<Longrightarrow>
   gensyn_iterate fb fl t = GRDone \<Longrightarrow>
   gensyn_sem t cp m m'"

| "\<And> t cp g r l fb fl m cp' m' m'' .
   gensyn_get t cp = Some (GRec g r l) \<Longrightarrow>
   rec_sem g r m m' cp fb fl \<Longrightarrow>
   gensyn_iterate fb fl t = GRPath cp' \<Longrightarrow>
   gensyn_sem t cp' m' m'' \<Longrightarrow>
   gensyn_sem t cp m m''"

end


end
