theory Relpath imports Gensyn Gensyn_Descend
begin

(* some more utilities for childpaths *)
fun droplast :: "'a list \<Rightarrow> 'a list option" where
"droplast [] = None"
| "droplast [h] = Some []"
| "droplast (h#t) = 
   (case droplast t of
    None \<Rightarrow> None
    | Some t' \<Rightarrow> Some (h#t'))"

(* when we are representing childpaths backwards (for easier induction) *)
type_synonym childpath_rev = "nat list"

fun droplast' :: "'a list \<Rightarrow> 'a list" where
"droplast' [] = []"
| "droplast' [h] = []"
| "droplast' (h#t) = h # droplast' t"

(* Path updates resulting from execution at a Gensyn node *)
datatype rel_update =
  Parent
  | Desc "childpath_rev"


(* NB: these are not canonical. *)
datatype relpath =
  RP (r_ancestor : "nat") (r_desc : "childpath_rev")

(* idea: relpathD captures the idea of
   - "navigate to the given childpath"
   - then "modify by the relpath"
*)
fun relpathD_rev :: "relpath \<Rightarrow> childpath_rev \<Rightarrow> childpath_rev option" where
"relpathD_rev (RP 0 desc) path = Some (desc @ path)"
| "relpathD_rev (RP (Suc n) desc) [] = None"
| "relpathD_rev (RP (Suc n) desc) (ph#pt) = relpathD_rev (RP n desc) (pt)"

fun relpath_update :: "relpath \<Rightarrow> rel_update \<Rightarrow> relpath" where
"relpath_update (RP n []) Parent = (RP (Suc n) [])"
| "relpath_update (RP n (ph#pt)) Parent = (RP n pt)"
| "relpath_update (RP n path) (Desc cp) = (RP n (cp @ path))"

fun childpath_rev_update :: "childpath_rev \<Rightarrow> rel_update \<Rightarrow> childpath_rev option" where
"childpath_rev_update [] Parent = None"
| "childpath_rev_update (ph#pt) Parent = Some (pt)"
| "childpath_rev_update path (Desc cp) = Some (cp @ path)"

lemma droplast'_suffix :
  shows "droplast' (l1 @ h # l2) = l1 @ droplast' (h # l2)"
proof(induction l1 arbitrary: h l2)
  case Nil
  then show ?case by auto
next
  case (Cons a l1)
  show ?case 
  proof(cases l1)
    case Nil' : Nil
    show ?thesis using Cons Nil' by(auto)
  next
    case Cons' : (Cons a' l1')
    show ?thesis using Cons Cons' by(auto)
  qed
qed

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc l x = l @ [x]"

lemma snoc_case :
  "\<exists> l' x . (h#t) = (snoc l' x)"
proof(induction t arbitrary: h)
  case Nil
  then show ?case by auto
next
  case (Cons a t)
  obtain l1 x where L1 : "a#t = snoc l1 x" using Cons(1)[of a] by(auto)

  then show ?case by auto
qed

lemma list_induct_app :
  assumes HNil : "P []"
  assumes HSing : "\<And> x . P [x]"
  assumes HApp : "\<And> l1 l2 . P l1 \<Longrightarrow> P l2 \<Longrightarrow> P (l1 @ l2)"
  shows "P l" using assms
proof(induction l arbitrary: P)
  case Nil
  then show ?case by auto
next
  case (Cons a l)

  have Conc' : "P l" using Cons(1)[of P, OF Cons(2) Cons(3) Cons(4)] by auto

  show ?case using Cons(4)[of "[a]" l, OF Cons(3) Conc'] 
    by auto
qed

lemma relpath_update_correct_rev :                            
  assumes H : "relpathD_rev r cp = Some cp'"
  shows "relpathD_rev (relpath_update r upd) cp =
         childpath_rev_update cp' upd" using assms
proof(induction cp arbitrary: r cp' upd)
  case Nil
  obtain anc desc where R : "r = RP anc desc" by(cases r; auto)

  then show ?case using Nil  apply(cases anc; auto) apply(cases upd; auto)
    apply(cases cp'; auto)
    done
next
  case (Cons cph cpt)

  obtain anc desc where R : "r = RP anc desc" by(cases r; auto)

  show ?case
  proof(cases anc)
    case 0
    show ?thesis 
    proof(cases upd)
      case Parent
      show ?thesis
      proof(cases desc)
        case Nil' : Nil
        then show ?thesis using 0 R Cons Parent by auto
      next
        case Cons' : (Cons dh dt)
        then show ?thesis using 0 R Cons Parent by auto
      qed
    next
      case (Desc up_desc)
      show ?thesis
      proof(cases desc)
        case Nil' : Nil
        then show ?thesis using 0 R Cons Desc by auto
      next
        case Cons' : (Cons dh dt)
        then show ?thesis using 0 R Cons Desc by auto
      qed
    qed
  next

    case (Suc anc')

    hence RelPath : "relpathD_rev (RP anc' desc) cpt = Some cp'" using Cons R by(auto)

    show ?thesis
    proof(cases upd)
      case Parent
      show ?thesis
      proof(cases desc)
        case Nil' : Nil
        then show ?thesis using Cons(1)[OF RelPath, of Parent] Suc R Parent
          by(auto)
      next
        case Cons' : (Cons dh dt)
        then show ?thesis using Cons(1)[OF RelPath, of Parent] Suc R Parent by(auto)
      qed
    next
      case (Desc up_desc)
      show ?thesis
      proof(cases desc)
        case Nil' : Nil
        then show ?thesis using Cons(1)[OF RelPath, of "Desc up_desc"] Suc R Desc by auto
      next
        case Cons' : (Cons dh dt)
        then show ?thesis using Cons(1)[OF RelPath, of "Desc up_desc"] Suc R Desc by auto
      qed
    qed
  qed
qed

definition relpathD :: "relpath \<Rightarrow> childpath \<Rightarrow> childpath option" where
"relpathD r cp =
  (case relpathD_rev r (rev cp) of
   None \<Rightarrow> None
   | Some cp' \<Rightarrow> Some (rev cp'))"

definition childpath_update :: "childpath \<Rightarrow> rel_update \<Rightarrow> childpath option" where
"childpath_update cp upd =
  (case childpath_rev_update (rev cp) upd of
   None \<Rightarrow> None
   | Some cp' \<Rightarrow> Some (rev cp'))"

lemma relpath_update_correct :                            
  assumes H : "relpathD r cp = Some cp'"
  shows "relpathD (relpath_update r upd) cp =
         childpath_update cp' upd"
proof(cases "relpathD_rev r (rev cp)")
  case None
  then show ?thesis using H
    by(auto simp add: relpathD_def childpath_update_def)
next
  case (Some cp'r)

  have Cp'_rev: "cp'r = rev cp'" using Some H by(auto simp add: relpathD_def childpath_update_def)

  show ?thesis 
  proof(cases "relpathD_rev (relpath_update r upd) (rev cp)")
    case None' : None

    show ?thesis using Some None'
    proof(cases "childpath_rev_update (rev cp') upd")
      case None'' : None
      then show ?thesis using Some None' by(auto simp add: relpathD_def childpath_update_def)
    next
      case Some'' : (Some y)
      then show ?thesis using Some None' relpath_update_correct_rev[OF Some] Cp'_rev
        by(auto)
    qed
  next
    case Some' : (Some x)
    then show ?thesis using Some Some' relpath_update_correct_rev[OF Some] Cp'_rev
      by(auto simp add: relpathD_def childpath_update_def)
  qed
qed





(* OK, so now we have this utility for relative paths. The game plan now:
- store relative paths in the state
- pass around a path which is used to find the actual nodes

how does this fit into Hoare triples though?

i think we should be able to leave the original childpath concrete.

so, when we are actually looking at sub-trees, this should make it easier.

*)

end