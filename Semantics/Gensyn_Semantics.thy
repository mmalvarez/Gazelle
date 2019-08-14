theory Gensyn_Semantics
  imports "../Gensyn" "../Gensyn_Descend"
begin

(* TODO:
break this file up into code and spec? *)

datatype ('x) gs_result =
  GRUnhandled
  | GRPath childpath
  | GRCrash
  | GRDone
  | GRFuel
  | GROther 'x

type_synonym gensyn_skel = "(unit, unit, unit) gensyn"

inductive nosem_base_sem::
  " 'g \<Rightarrow> 
    'b \<Rightarrow>
    'mstate \<Rightarrow> 
    'mstate \<Rightarrow> 
      childpath \<Rightarrow>
      ('b, 'r, 'g) gensyn \<Rightarrow>  
      ('rxb) gs_result \<Rightarrow>
      bool"
  where  "nosem_base_sem _ _ _ _ _ _ GRUnhandled"


(*
fun nosem_base_sem_exec ::
  "('b, 'r, 'g) gensyn \<Rightarrow>
    'g \<Rightarrow> 
    'b \<Rightarrow> 
    childpath \<Rightarrow> 
    'mstate \<Rightarrow> 
    (childpath option *
    'mstate) option"
  where "nosem_base_sem_exec _ _ _ _ _ = None"
*)

inductive nosem_rec_sem ::
  " 'g \<Rightarrow> 
    'r \<Rightarrow> 
    'mstate \<Rightarrow> 
    'mstate \<Rightarrow> 
      childpath \<Rightarrow>
      ('b, 'r, 'g) gensyn \<Rightarrow>  
      ('rxr) gs_result \<Rightarrow>
      bool"
  where "nosem_rec_sem _ _ _ _ _ _ GRUnhandled"

(*
fun nosem_rec_sem_exec ::
  "('b, 'r, 'g) gensyn \<Rightarrow>
    'g \<Rightarrow> 
    'r \<Rightarrow> 
    childpath \<Rightarrow> 
    'mstate \<Rightarrow> 
    (childpath option *
    'mstate) option"
  where "nosem_rec_sem_exec _ _ _ _ _ = None"
*)

(* idea: we distinguish an "unhandled" case, which allows us to
   signal that this particular semantics does not handle this case, but some other one may
   TODO: do we want an explicit "crash"/failure as well? i think we probably actually do not.
*)

fun gs_strip :: "('a, 'b, 'c) gensyn \<Rightarrow> gensyn_skel" where
"gs_strip (GBase _ _) = GBase () ()"
| "gs_strip (GRec _ _ l) = GRec () () (map gs_strip l)"

locale Gensyn_Semantics =
  (* fixes/assumes go here *)
  (* NB: these are "small steps" in that they return a new childpath and don't do a full
         execution *)
  (* we are making these parametric in gensyn parameters so that
           they can't do weird computations over tree other than
           calculating new childpath
    
     this assumes that we do not need to do extra state updates when walking the
     syntax tree - but we should not
*)


(* one option: separate base from result. this seems like an unnecessary extra
level of indirection. *)
(*
  fixes base_sem :: " 'g \<Rightarrow> 
                      'b \<Rightarrow>  
                      'mstate \<Rightarrow> 
                      'result \<Rightarrow>
                      'mstate \<Rightarrow> 
                      bool"

fixes base_result_sem :: "'result \<Rightarrow>
                     gensyn_skel \<Rightarrow>
                     childpath \<Rightarrow>
                     ('cb, 'xb) gs_result \<Rightarrow> (* should output be an option? *)
                     bool"


  fixes rec_sem :: "'g \<Rightarrow>
                    'r \<Rightarrow>
                    'mstate \<Rightarrow>
                    'result \<Rightarrow>
                    'mstate \<Rightarrow>
                    bool"

fixes rec_result_sem :: "'result \<Rightarrow>
                     gensyn_skel \<Rightarrow>
                     childpath \<Rightarrow>
                     ('cr, 'xr) gs_result \<Rightarrow> (* should output be an option? *)
                     bool"
*)
(* second option: combine *)
  fixes base_sem :: " 'g \<Rightarrow> 
                      'b \<Rightarrow>
                      'mstate \<Rightarrow> 
                      'mstate \<Rightarrow> 
                      childpath \<Rightarrow>
                      ('b, 'r, 'g) gensyn \<Rightarrow>  
                      ('xr) gs_result \<Rightarrow>
                      bool"

  fixes rec_sem :: "'g \<Rightarrow>
                    'r \<Rightarrow>
                    'mstate \<Rightarrow>
                    'mstate \<Rightarrow>
                    childpath \<Rightarrow>
                    ('b, 'r, 'g) gensyn \<Rightarrow>
                    ('xr) gs_result \<Rightarrow>
                    bool"

(* question: dealing with state abstraciton.
   do we want to allow different notions of mstate as long as we have the
  ability to project in/out?

  let's deal with this issue later
*)

begin


(* NB this is a big step semantics. sufficient for Ethereum, but perhaps not enough
   for other platforms
   *)
inductive gensyn_sem ::
  "('b, 'r, 'g) gensyn \<Rightarrow>
   childpath \<Rightarrow>
   'mstate \<Rightarrow>
   'mstate \<Rightarrow>
   bool
  "
  where
  "\<And> t cp g b m m' .
    gensyn_get t cp = Some (GBase g b) \<Longrightarrow>
    base_sem g b m m' cp t GRDone \<Longrightarrow>
    gensyn_sem t cp m m'"

| "\<And> t cp g b m cp' m' m'' .
    gensyn_get t cp = Some (GBase g b) \<Longrightarrow>
    base_sem g b m m' cp t (GRPath cp') \<Longrightarrow>
    gensyn_sem t cp' m' m'' \<Longrightarrow>
    gensyn_sem t cp m m''"

| "\<And> t cp g r l m m' .
   gensyn_get t cp = Some (GRec g r l) \<Longrightarrow>
   rec_sem g r m m' cp t GRDone \<Longrightarrow>
   gensyn_sem t cp m m'"

| "\<And> t cp g r l m cp' m' m'' .
   gensyn_get t cp = Some (GRec g r l) \<Longrightarrow>
   rec_sem g r m m' cp t (GRPath cp') \<Longrightarrow>
   gensyn_sem t cp' m' m'' \<Longrightarrow>
   gensyn_sem t cp m m''"

end

interpretation Gensyn_Semantics_Nosem : Gensyn_Semantics
  nosem_base_sem nosem_rec_sem
  done

(* i don't know if these are actually useful *)
fun unskel :: "(gensyn_skel \<Rightarrow> ('a, 'b, 'c) gensyn)" where
"unskel (GBase () ()) = GBase undefined undefined"
| "unskel (GRec () () l) = GRec undefined undefined (map unskel l)"
  
fun skel_lift1 :: "(('a, 'b, 'c) gensyn \<Rightarrow> bool) \<Rightarrow> gensyn_skel \<Rightarrow> bool"
  where
"skel_lift1 p s = p (unskel s)"

fun skel_lift2 :: "(gensyn_skel \<Rightarrow> bool) \<Rightarrow> ('a, 'b, 'c) gensyn \<Rightarrow> bool" where
"skel_lift2 p s = p (gs_strip s)"

(* test - numnodes predicate *)
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

fun gensyn_two_nodes :: "('a, 'b, 'c) gensyn \<Rightarrow> bool" where
 "gensyn_two_nodes g = (gensyn_numnodes g = 2)"

lemma preds_equal :
    "skel_lift1 gensyn_two_nodes (GRec ()() [])"
  apply(simp)
  done

(* in order to characterize when this works, though, we are going to
   need a way to characterize what the predicate is actually looking at *)

locale Gensym_Semantics_Exec =
  fixes base_sem_exec :: "
                      'g \<Rightarrow> 
                      'b \<Rightarrow> 
                      'mstate \<Rightarrow>
                      childpath \<Rightarrow> 
                      ('b, 'r, 'g) gensyn \<Rightarrow> 
                      ('xr gs_result *
                      'mstate) option"

  fixes rec_sem_exec :: "
                      'g \<Rightarrow>
                      'r \<Rightarrow>
                      'mstate \<Rightarrow>
                      childpath \<Rightarrow>
                      ('b, 'r, 'g) gensyn \<Rightarrow>
                      ('xr gs_result *
                      'mstate) option"

begin

(* TODO: deal with the rest of the exec stuff later *)

(* fueled interpreter for semantics *)
(* TODO: count down only for backwards jumps? *)
fun gensyn_sem_exec ::
  "('b, 'r, 'g) gensyn \<Rightarrow>
   childpath \<Rightarrow>
   'mstate \<Rightarrow>
    nat \<Rightarrow>
   'mstate option" 
  where
  "gensyn_sem_exec t cp m 0 = None"

| "gensyn_sem_exec t cp m (Suc n) =
    (case gensyn_get t cp of
     None \<Rightarrow> None
     | Some (GBase g b) \<Rightarrow>
       (case base_sem_exec g b m cp t of
             None \<Rightarrow> None
             | Some (GRDone, m') \<Rightarrow> Some m'
             | Some (GRPath cp', m') \<Rightarrow> gensyn_sem_exec t cp' m' n
             | Some (_, _) \<Rightarrow> None)
     | Some (GRec g r l) \<Rightarrow>
        (case rec_sem_exec g r m cp t of
             None \<Rightarrow> None
             | Some (GRDone, m') \<Rightarrow> Some m'
             | Some (GRPath cp', m') \<Rightarrow> gensyn_sem_exec t cp' m' n
             | Some (_, _) \<Rightarrow> None))"

lemma gensyn_sem_exec_morefuel :
  assumes H: "gensyn_sem_exec t cp m n = Some m'"
  (*assumes Hn' : "n' > n"*)
  shows "gensyn_sem_exec t cp m (Suc n) = Some m'" using H
proof(induction n arbitrary: t cp m m')
  case 0
  then show ?case by auto
next
  case (Suc nx)
  thus ?case
  proof(cases "gensyn_get t cp")
    case None
    then show ?thesis using Suc by auto
  next
    case (Some a)
    then show ?thesis 
    proof(cases a)
      case (GBase x11 x12)
      then show ?thesis using Suc Some
      proof(cases "base_sem_exec x11 x12 m cp t")
        assume None': "base_sem_exec x11 x12 m cp t = None"
        then show ?thesis using Suc Some GBase by auto
      next
        fix stm'
        assume Some': "base_sem_exec x11 x12 m cp t = Some stm'"
        then show ?thesis
        proof(cases stm')
          case (Pair st' m'')
          then show ?thesis using Pair Some' GBase Some Suc
            apply(case_tac st', auto)
            done
        qed
      qed
    next
      case (GRec x21 x22 x23)
      then show ?thesis
      proof(cases "rec_sem_exec x21 x22 m cp t")
        assume None' :"rec_sem_exec x21 x22 m cp t = None"
        then show ?thesis using Suc Some GRec by auto
      next
        fix stm'
        assume Some': "rec_sem_exec x21 x22 m cp t = Some stm'"
        then show ?thesis
        proof(cases stm')
          case (Pair st' m'')
          then show ?thesis using Pair Some' GRec Some Suc
            apply(case_tac st', auto)
            done
        qed
      qed
    qed
  qed
qed

fun gsx_base_sem :: " 'g \<Rightarrow> 
                      'b \<Rightarrow> 
                      'mstate \<Rightarrow>
                      'mstate \<Rightarrow>
                      childpath \<Rightarrow> 
                      ('b, 'r, 'g) gensyn \<Rightarrow>
                      ('xr) gs_result \<Rightarrow>
                      bool"
  where
"gsx_base_sem g b m m' cp t res = 
    (case base_sem_exec g b m cp t of
        None \<Rightarrow> m' = m \<and> res = GRFuel
        | Some (res', m'') \<Rightarrow> m' = m'' \<and> res = res')"

fun gsx_rec_sem :: "'g \<Rightarrow>
                    'r \<Rightarrow>
                    'mstate \<Rightarrow>
                    'mstate \<Rightarrow>
                    childpath \<Rightarrow>
                    ('b, 'r, 'g) gensyn \<Rightarrow>
                    ('xr) gs_result \<Rightarrow>
                    bool"
  where
"gsx_rec_sem g r m m' cp t res =
  (case rec_sem_exec g r m cp t of
    None \<Rightarrow> m' = m \<and> res = GRFuel
    | Some (res', m'') \<Rightarrow> m' = m'' \<and> res = res')"

fun gsx_gensyn_sem ::
"('b, 'r, 'g) gensyn \<Rightarrow>
   childpath \<Rightarrow>
   'mstate \<Rightarrow>
   'mstate \<Rightarrow>
   bool
  "
where
"gsx_gensyn_sem t cp m m' =  (\<exists> fuel . gensyn_sem_exec t cp m fuel = Some m')"

(* standard version of the semantics *)
interpretation Gensyn_Exec_Semantics : Gensyn_Semantics
 gsx_base_sem gsx_rec_sem
  done

lemma gensyn_exec_eq_l2r :
  fixes t cp m m'
  shows  "Gensyn_Exec_Semantics.gensyn_sem t cp m m' \<Longrightarrow> gsx_gensyn_sem t cp m m'"
  proof(induction rule: Gensyn_Exec_Semantics.gensyn_sem.induct)
case (1 t cp g b m m')
  then show ?case
    apply(simp)
    apply(rule_tac x = 1 in exI) apply(auto)
    apply(case_tac "base_sem_exec g b m cp t", auto)
    done
next
case (2 t cp g b m cp' m' m'')
  then show ?case
    apply(simp)
    apply(auto)
    apply(rule_tac x = "Suc fuel" in exI) apply(auto)
    apply(case_tac "base_sem_exec g b m cp t", auto)
    done
next
  case (3 t cp g r l m m')
  then show ?case
    apply(simp)
    apply(rule_tac x = 1 in exI) apply(auto)
    apply(case_tac "rec_sem_exec g r m cp t", auto)
    done
next
  case (4 t cp g r l m cp' m' m'')
  then show ?case
    apply(simp)
    apply(auto)
    apply(rule_tac x = "Suc fuel" in exI) apply(auto)
    apply(case_tac "rec_sem_exec g r m cp t", auto)
    done
qed

lemma gensyn_exec_eq_r2l :
  fixes fuel
  shows "\<And> t cp m m'. gensyn_sem_exec t cp m (fuel) = Some m' \<Longrightarrow> Gensyn_Exec_Semantics.gensyn_sem t cp m m'"
  proof(induction fuel)
    case 0
    then show ?case by auto
  next
    case (Suc fuel)
    then show ?case 
    proof(cases "gensyn_get t cp")
      case None
      then show ?thesis using Suc by auto
    next
      case (Some a)
      then show ?thesis using Suc
      proof(cases a)
        case (GBase x11 x12) then show ?thesis using Some Suc
        proof(cases "base_sem_exec x11 x12 m cp t")
          assume None' : "base_sem_exec x11 x12 m cp t = None"
          thus ?thesis using GBase Some Suc by auto
        next
          fix a'
          assume Some' : "base_sem_exec x11 x12 m cp t = Some a'"
          thus ?thesis using GBase Some Suc
          proof(cases a')
            case (Pair a'' b)
            then show ?thesis using Some' GBase Some Suc
              apply(simp)
              apply(case_tac a'', auto simp add: Gensyn_Semantics.gensyn_sem.intros)
              done
          qed
        qed
      next
        case (GRec x21 x22 x23)
        then show ?thesis using Some Suc
          proof(cases "rec_sem_exec x21 x22 m cp t")
            assume None' : "rec_sem_exec x21 x22 m cp t = None"
            thus ?thesis using GRec Some Suc by auto
          next
        fix a'
        assume Some' : "rec_sem_exec x21 x22 m cp t = Some a'"
        thus ?thesis using GRec Some Suc
        proof(cases a')
          case (Pair a'' b)
            then show ?thesis using Some' GRec Some Suc
              apply(simp)
              apply(case_tac a'', auto simp add: Gensyn_Semantics.gensyn_sem.intros)
              done
          qed
        qed
      qed
    qed
qed


interpretation Gensyn_Exec_Semantics_Fuel : Gensyn_Semantics
 gsx_base_sem gsx_rec_sem
 rewrites Crew : "Gensyn_Exec_Semantics.gensyn_sem = gsx_gensyn_sem"
proof(unfold_locales)
  have Goal : "\<And> t cp m m' . Gensyn_Exec_Semantics.gensyn_sem t cp m m' = gsx_gensyn_sem t cp m m'" 
  proof - 
    fix t cp m m'
    show "Gensyn_Exec_Semantics.gensyn_sem t cp m m' = gsx_gensyn_sem t cp m m'"
      using gensyn_exec_eq_l2r
                             gensyn_exec_eq_r2l  by auto
  qed

    thus "Gensyn_Exec_Semantics.gensyn_sem = gsx_gensyn_sem" by blast
  qed

end
end