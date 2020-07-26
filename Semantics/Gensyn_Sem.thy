theory Gensyn_Sem
  imports "../Gensyn" "../Gensyn_Descend" "../MergeableTc/Mergeable"
begin

(* TODO:
break this file up into code and spec? *)




(* originally had ('x option) gensyn as argument *)
type_synonym ('x, 'mstate, 'xr) x_semr =
  "'x \<Rightarrow>
    'x gensyn \<Rightarrow>  
    childpath \<Rightarrow>
    'mstate \<Rightarrow> 
    'mstate \<Rightarrow> 
    ('xr) gs_result \<Rightarrow>
    bool" 

type_synonym ('x, 'mstate, 'xr) x_sem =
  "'x \<Rightarrow>
    'x gensyn \<Rightarrow>  
    childpath \<Rightarrow>
    'mstate \<Rightarrow> 
    ('xr) gs_result * 'mstate"

type_synonym ('x, 'mstate) x_sem' =
  "'x \<Rightarrow>
   ((gensyn_skel * unit gs_result) * 'mstate) \<Rightarrow>
   ((gensyn_skel * unit gs_result) * 'mstate)"

definition xsem :: "('x, 'mstate) x_sem' \<Rightarrow> ('x, 'mstate, unit) x_sem" where
  "xsem f' x t cp m =
    (case f' x ((gs_sk t, (GRPath cp)), m) of
      ((t', r'), m') \<Rightarrow> (r', m'))"

inductive gensyn_sem ::
  "('a, 'b, 'c) x_semr \<Rightarrow>
   ('a) gensyn \<Rightarrow>
   childpath \<Rightarrow>
   'b \<Rightarrow>
   'b \<Rightarrow>
   bool
  "
  where
  "\<And> x_sem t cp x l m m' .
    gensyn_get t cp = Some (G x l) \<Longrightarrow>
    x_sem x t cp m m' GRDone \<Longrightarrow>
    gensyn_sem x_sem t cp m m'"

| "\<And> x_sem t cp x l m cp' m' m'' .
    gensyn_get t cp = Some (G x l) \<Longrightarrow>
    x_sem x t cp m m' (GRPath cp') \<Longrightarrow>
    gensyn_sem x_sem t cp' m' m'' \<Longrightarrow>
    gensyn_sem x_sem t cp m m''"

(* first bool. True = done, False = sync *)
(* do we need to support multiple layers of recursion w/r/t syncing?
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