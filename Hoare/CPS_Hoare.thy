theory CPS_Hoare imports 
 "../Gensyn" "../Gensyn_Descend" "../Mergeable/Mergeable"
 "../Lifting/LiftUtils" "../Lifting/LiftInstances" "../Lifting/LangCompSimple"
begin

(* ok, so in order to adapt CPS hoare triples into this context,
   we need a more "normal-looking" system where we can separate
   continuations from state *)

datatype 'syn s_error =
  Exec 'syn 
  | BadPath
  | NoFuel
  | Done
  | Halted (* halted = too much fuel *)

fun s_error_safe :: "'x s_error \<Rightarrow> bool" where
"s_error_safe (Exec _) = True"
| "s_error_safe Done = True"
| "s_error_safe _ = False"

(* we also need to be able to separate sub-syntax from entire tree *)

record ('syn, 'mstate) sem' =
  s_sem :: "'syn \<Rightarrow> 'mstate \<Rightarrow> 'mstate"

record ('syn, 'mstate) sem = "('syn, 'mstate) sem'" +
  s_next :: "'mstate \<Rightarrow> ('syn s_error)"


(* need to deal with this difference around halting behavior. *)
(*
definition sem_step ::
  "('x, 'mstate) sem \<Rightarrow>
   'mstate \<Rightarrow>
   ('mstate * 'x s_error)" where
"sem_step gs m =
  (case s_next gs m of
    Done \<Rightarrow> (m, Halted)
    | Exec sub \<Rightarrow> (s_sem gs sub m, Exec sub)
    | f \<Rightarrow> (m, f))"
*)

definition sem_step ::
  "('x, 'mstate) sem \<Rightarrow>
   'mstate \<Rightarrow>
   ('mstate option)" where
"sem_step gs m =
  (case s_next gs m of
    Exec sub \<Rightarrow> Some (s_sem gs sub m)
    | f \<Rightarrow> None)"


(* maybe use a relational small-step, relate it to the executable one? *)
(* transitive closure? *)
fun sem_exec ::
  "('x, 'mstate) sem \<Rightarrow>
   nat \<Rightarrow>
   'mstate \<Rightarrow>
   ('mstate * 'x s_error)" where
"sem_exec gs 0 m = (m, s_next gs m )"
| "sem_exec gs (Suc n) m =
   (case s_next gs m of
    Done \<Rightarrow> (m, Halted)
    | Exec sub \<Rightarrow> sem_exec gs n (s_sem gs sub m)
    | f \<Rightarrow> (m, f))"

inductive sem_step_p ::
  "('x, 'mstate) sem \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool"
  where
"\<And> (m :: 'mstate) (m' :: 'mstate) .
 s_next gs m = Exec sub \<Longrightarrow> 
 s_sem gs sub m = m' \<Longrightarrow>
 sem_step_p gs m m'"

definition sem_exec_p ::
  "('x, 'mstate) sem \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool" where
"sem_exec_p gs \<equiv>
  (rtranclp (sem_step_p gs))"

lemma sem_step_p_sem_step :
  assumes H : "sem_step_p gs m m'"
  shows "sem_step gs m = Some m'" using H
proof(cases rule: sem_step_p.cases)
  case (1 sub)
  then show ?thesis 
    by(auto simp add: sem_step_def)
qed

lemma sem_step_sem_step_p :
  assumes H : "sem_step gs m = Some m'"
  shows "sem_step_p gs m m'" using H
  by(auto simp add: sem_step_def split: s_error.splits intro: sem_step_p.intros)

lemma sem_step_exec1 :
  assumes H : "sem_step gs m = Some m'"
  shows "\<exists> s . (sem_exec gs 1 m = (m', s))" using H
  by(auto simp add: sem_step_def  split:s_error.splits)

lemma sem_exec1_step :
  assumes H : "(sem_exec gs 1 m = (m', s))"
  assumes H' : "s_error_safe s"
  shows "sem_step gs m = Some m'" using assms
  by(auto simp add: sem_step_def split:s_error.splits)

(*
lemma sem_exec_snd :
  assumes H : "sem_exec gs n m = (m', x)"
  shows "x = s_next gs m'" using assms
proof(induction n arbitrary: m m' x)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case 
    apply(auto split: s_error.splits)
qed
*)


definition imm_safe :: "('x, 'mstate) sem \<Rightarrow> 'mstate \<Rightarrow> bool" where
"imm_safe gs m \<equiv>
 ((s_next gs m = Done) \<or>
  (\<exists> x . s_next gs m = Exec x \<and> s_error_safe (s_next gs (s_sem gs x m))))"

definition safe :: "('x, 'mstate) sem \<Rightarrow> 'mstate \<Rightarrow> bool" where
"safe gs m \<equiv>
  (\<forall> m' . sem_exec_p gs m m' \<longrightarrow> imm_safe gs m')"

(* ugh.... still, would be great to have a way to separate state from
  "next control".
maybe we are ok? just add the qualification that s_next is the syntax of the command?
*)

(*
definition safe :: "('x, 'mstate) sem \<Rightarrow> 'mstate \<Rightarrow> bool" where
"safe gs m \<equiv>
 (imm_safe gs m \<or>
 ())
*)

(* classic question: want constraint on command below or above line? *)
(* universally quantify over gs? *)
definition G :: "('x, 'mstate) sem \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> 'x \<Rightarrow> bool" where
"G gs P c =
  (\<forall> m . P m \<longrightarrow> s_next gs m = Exec c \<longrightarrow> safe gs m)"

(* tricky - now we need to quantify over programs
that would be gs
this is why we are splitting up gs
 *)
definition HT :: "('x, 'mstate) sem \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> 'x \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> bool" where
"HT gs P c P' =
  

end