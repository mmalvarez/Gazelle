theory Gensyn_Sem_Multi
  imports "../Gensyn" "../Gensyn_Descend" "../MergeableTc/Mergeable"
begin

(*
 * TODO: what is this for? Is this useful?
*)

(* TODO:
break this file up into code and spec? *)

datatype ('x) gs_result =
  GRPath childpath
  | GRCrash
  | GRDone
  | GRUnhandled
  | GRSync "'x gs_result"
  | GROther 'x

type_synonym gensyn_skel = "(unit) gensyn"

type_synonym param_gensyn = "(_) gensyn"

(* originally had ('x option) gensyn as argument *)
type_synonym ('x, 'mstate) x_semr =
  "'x \<Rightarrow>
    'x gensyn \<Rightarrow>  
    childpath gensyn \<Rightarrow>
    'mstate \<Rightarrow> 
    'mstate \<Rightarrow> 
    childpath gensyn \<Rightarrow>
    bool" 

type_synonym ('x, 'mstate, 'xr) x_sem =
  "'x \<Rightarrow>
    'x gensyn \<Rightarrow>  
    childpath \<Rightarrow>
    'mstate \<Rightarrow> 
    ('xr) gs_result * 'mstate"

fun cpg_get :: "childpath gensyn \<Rightarrow> childpath" where
"cpg_get (G cp _) = cp"

inductive gensyn_sem ::
  "('a, 'b) x_semr \<Rightarrow>
   ('a) gensyn \<Rightarrow>
   childpath gensyn \<Rightarrow>
   'b \<Rightarrow>
   'b \<Rightarrow>
   bool
  "
  where
(* "done" case *)
  "\<And> x_sem t cps x l m m' cps' .
    gensyn_get t (cpg_get cps) = Some (G x l) \<Longrightarrow>
    x_sem x t cps m m' (G [] []) \<Longrightarrow>
    gensyn_sem x_sem t cps m m'"

(* *)
| "\<And> x_sem t cp x l m cp' m' m'' .
    gensyn_get t (cpg_get cps) = Some (G x l) \<Longrightarrow>
    x_sem x t cp m m' (GRPath cp') \<Longrightarrow>
    gensyn_sem x_sem t cp' m' m'' \<Longrightarrow>
    gensyn_sem x_sem t cp m m''"


(* first bool. True = done, False = sync *)
(* do we need to support multiple layers of recursion w/r/t syncing?
*)

(*
inductive gensyn_sem_sync ::
  "('a, 'b, 'c) x_semr \<Rightarrow>
   ('a) gensyn \<Rightarrow>
   childpath \<Rightarrow>
   'b \<Rightarrow>
   'b \<Rightarrow>
   bool \<Rightarrow>
   bool"
  where
  "gensyn_get t cp = Some (G x l) \<Longrightarrow>
   x_sem x t cp m m' GRSync \<Longrightarrow>
   gensyn_sem_sync x_sem t cp m m' False"

| "gensyn_get t cp = Some (G x l) \<Longrightarrow>
   x_sem x t cp m m' GRDone \<Longrightarrow>
   gensyn_sem_sync x_sem t cp m m' True"

| "gensyn_get t cp = Some (G x l) \<Longrightarrow>
   x_sem x t cp m m' (GRPath cp') \<Longrightarrow>
   gensyn_sem_sync x_sem t cp' m' m'' b \<Longrightarrow>
   gensyn_sem_sync x_sem t cp m m'' b"
*)

fun get_children' ::
  "'a gensyn list \<Rightarrow> childpath \<Rightarrow> nat \<Rightarrow> childpath list" where
"get_children' [] cp _ = []"
| "get_children' (h#t) cp n =
    (n#cp) # get_children' t cp (n+1)"

(* idea: use get_children' to compute list of nodes to visit
   when we run out of paths, we always go to the next one
   when list is empty, we are done with execution
   how do sync points fit into this? should be tied to nodes. *)

inductive gensyn_sem_split_small ::
  "('a, 'b) x_semr set \<Rightarrow>
   ('a) gensyn \<Rightarrow>
   childpath \<Rightarrow>
   'b \<Rightarrow>
   ('b * 'c childpath gensyn) set \<Rightarrow>
   bool"
  where
  "gensyn_get t cp = Some (G x l) \<Longrightarrow>
   S = { str .
    \<exists> st r f . str = (st, r) \<and> f \<in> x_sem \<and>
    f x t cp m m' r } \<Longrightarrow>
   gensyn_sem_split_small x_sem t cp m S"

inductive gensyn_sem_split_onepath ::
  "('a, 'b, 'c) x_semr set \<Rightarrow>
   ('a) gensyn \<Rightarrow>
   childpath \<Rightarrow>
   'b \<Rightarrow>
   'b \<Rightarrow> 'c gs_result \<Rightarrow>
   bool"
  where
"gensyn_sem_split_small x_sem t cp m S \<Longrightarrow>
 (m', GRSync r') \<in> S \<Longrightarrow>
 gensyn_sem_split_onepath x_sem t cp m m' (GRSync r')"

| "gensyn_sem_split_small x_sem t cp m S \<Longrightarrow>
   (m', GRPath cp') \<in> S \<Longrightarrow>
   gensyn_sem_split_onepath x_sem t cp' m' m'' r \<Longrightarrow>
   gensyn_sem_split_onepath x_sem t cp m m' r"

(* NB: this means we are "ignoring" nonterminating executions. this is probably bad. *)
inductive gensyn_sem_split_multipath ::
  "('a, 'b :: Mergeable, 'c) x_semr set \<Rightarrow>
   ('a) gensyn \<Rightarrow>
   childpath \<Rightarrow>
   'b \<Rightarrow>
   'b \<Rightarrow> 'c gs_result \<Rightarrow>
   bool" where
"S = {m'r' . \<exists> m' r' . m'r' = (m', r') \<and> gensyn_sem_split_onepath x_sem t cp m m' r' } \<Longrightarrow>
 snd ` S = {GRSync r} \<Longrightarrow>
 is_sup (fst ` S) m' \<Longrightarrow>
 gensyn_sem_split_multipath x_sem t cp m m' r"

(* idea: push forward until everything is Sync*)
(* do we want to allow stuttering steps? *)
(*
inductive gensyn_sem_split_multi ::
  "('a, 'b :: Mergeable, 'c) x_semr set \<Rightarrow>
   ('a) gensyn \<Rightarrow>
   childpath \<Rightarrow>
   'b \<Rightarrow>
   'b \<Rightarrow>
   'c gs_result \<Rightarrow>
   bool"
  where
"gensyn_sem_split_small x_sem t cp m S \<Longrightarrow>
 snd ` S = {GRSync r} \<Longrightarrow>
 is_sup (fst ` S) m' \<Longrightarrow>
 gensyn_sem_split_multi x_sem t cp m m' r"

| "gensyn_sem_split_small x_sem t cp m S \<Longrightarrow>
   S = Sync \<union> Path \<Longrightarrow>
   Sync = { str . str \<in> S \<and> (\<exists> st r' . str = (st, GRSync r'))} \<Longrightarrow>
   Path = { str . str \<in> S \<and> (\<exists> st cp' . str = (st, GRPath cp'))} \<Longrightarrow>
   Final = { str'' . 
      \<exists> st cp' st'' r'' . str'' = (st'', r'') \<and>
      (st, GRPath cp') \<in> Path \<and>
      gensyn_sem_split_multi x_sem t cp st st'' r'' } \<Longrightarrow>
   is_sup (fst ` Final) m' \<Longrightarrow>
   gensyn_sem_split_multi x_sem t cp m m' (GRDone)"
*)

(* set of ending states, which need an upper bound
look only at Done vs Path?
  - idea: if Done, go into state
    - or, maybe we want some kind of "sync" state
  - if Path, then we want to follow another step and then compress
    - what to do with crashes? exclude them, or include final state before crash?
 *)
(*
inductive gensyn_sem_split ::
  "('a, 'b ::Mergeable, unit) x_semr set \<Rightarrow>
   'a gensyn \<Rightarrow>
   childpath \<Rightarrow>
   'b \<Rightarrow>
   'b \<Rightarrow>
   bool" where
"gensyn_get t cp = Some (G x l) \<Longrightarrow>
 SD = { stcp . (\<exists> st' . \<exists> f \<in> x_sems .
                  stcp = (st', cp') \<and>
                  f x t cp m st (GRDone)) } \<Longrightarrow>
 SP = { stcp . (\<exists> st' . \<exists> cp' . \<exists> f \<in> x_sems .
                  stcp = (st', cp') \<and>
                  f x t cp m st (GRPath cp')) } \<Longrightarrow>
 SD' = {stcp' . (\<exists> st'' cp'' st' cp' . 
                    (st', cp') \<in> SD \<and>
                    (gensyn_sem_split x_sems t cp' st' st''))} \<Longrightarrow>
 gensyn_sem_split x_sems t cp m m'"
*)



(*
*)

fun gensyn_sem_exec ::
  "('a, 'b, 'c) x_sem \<Rightarrow>
   ('a) gensyn \<Rightarrow>
   childpath \<Rightarrow>
   'b \<Rightarrow>
    nat \<Rightarrow>
   'b option" 
  where
  "gensyn_sem_exec x_sem t cp m 0 = None"

| "gensyn_sem_exec x_sem t cp m (Suc n) =
    (case gensyn_get t cp of
     None \<Rightarrow> None
     | Some (G x l) \<Rightarrow>
       (case x_sem x t cp m of
              (GRDone, m') \<Rightarrow> Some m'
             | (GRPath cp', m') \<Rightarrow> gensyn_sem_exec x_sem t cp' m' n
             | (_, _) \<Rightarrow> None))"


lemma gensyn_sem_exec_morefuel :
  assumes H: "gensyn_sem_exec x_sem t cp m n = Some m'"
  shows "gensyn_sem_exec x_sem t cp m (Suc n) = Some m'" using H
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
      case (G x l)
      then show ?thesis
      proof(cases "x_sem x t cp m")
        case (Pair st' m'')
        then show ?thesis using Pair G Some Suc
          by(cases st', auto)
       qed
    qed
  qed
qed

definition gensyn_rel ::
  "('a, 'b, 'c) x_sem \<Rightarrow> ('a, 'b, 'c) x_semr" where
"gensyn_rel sem = 
  (\<lambda> x t c st st' r .
    (sem x t c st = (r, st')))"

(* TODO: need to translate relational and boolean x_sem *)
lemma gensyn_exec_eq_l2r :
  assumes H : "gensyn_sem x_semr t cp m1 m2"
  assumes H' : "x_semr = gensyn_rel x_sem"
  shows  "\<exists> fuel . gensyn_sem_exec x_sem t cp m1 fuel = Some m2"  using H H'
proof(induction rule: gensyn_sem.induct)
  case (1 x_sem' t cp x b m1 m2 )
    have "gensyn_sem_exec x_sem t cp m1 1 = Some m2" using 1 H'
      by(auto simp add:gensyn_rel_def split:prod.splits gs_result.splits)
    thus ?case by fast
  next
    case (2 x_sem' t cp x b m cp' m' m'')
    obtain fuel where Hfuel : "gensyn_sem_exec x_sem t cp' m' fuel = Some m''" using 2 by(auto)
    hence "gensyn_sem_exec x_sem t cp m (Suc fuel) = Some m''" using 2
      by(auto simp add:gensyn_rel_def split:prod.splits gs_result.splits)
    thus ?case by fast
  next
qed


lemma gensyn_exec_eq_r2l :
  assumes H : "gensyn_sem_exec x_sem t cp m (fuel) = Some m' "
  shows "gensyn_sem (gensyn_rel x_sem) t cp m m'" using H
  proof(induction fuel arbitrary: x_sem t cp m m')
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
        case(G x l)
        then show ?thesis using Some Suc
        proof(cases "x_sem x t cp m")
          case (Pair a'' b)
          then show ?thesis using G Some Suc
            by(auto intro:gensyn_sem.intros simp add:gensyn_rel_def split:gs_result.splits)
        qed
      qed
    qed
  qed

lemma gensyn_exec_agree :
  assumes H : "x_semr = gensyn_rel x_sem"
  shows "gensyn_sem x_semr = (\<lambda> t cp m m' . \<exists> fuel . gensyn_sem_exec x_sem t cp m fuel = Some m')"
proof(-)
  have Goal' : "\<And> t cp m m' . gensyn_sem x_semr t cp m m' = (\<exists> fuel . gensyn_sem_exec x_sem t cp m fuel = Some m')" 
  proof(-)
    fix t cp m m'
    show "gensyn_sem x_semr t cp m m' = (\<exists> fuel . gensyn_sem_exec x_sem t cp m fuel = Some m')"
      using H gensyn_exec_eq_l2r[of x_semr t cp m m' x_sem] gensyn_exec_eq_r2l[of x_sem t cp m _ m']
      by(auto simp add:gensyn_rel_def)
  qed
  
  show "gensyn_sem x_semr = (\<lambda>t cp m m'. \<exists>fuel. gensyn_sem_exec x_sem t cp m fuel = Some m')" 
    by((rule ext)+; rule Goal')
qed

end