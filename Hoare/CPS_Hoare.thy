theory CPS_Hoare imports 
 "../Gensyn" "../Gensyn_Descend" "../Mergeable/Mergeable"
 "../Lifting/LiftUtils" "../Lifting/LiftInstances" "../Lifting/LangCompSimple"
 "../Relpath" "../Semantics/Gensyn_Sem_Small" "Hoare"
begin

(* ok, so in order to adapt CPS hoare triples into this context,
   we need a more "normal-looking" system where we can separate
   continuations from state *)

(* TODO: we don't really need gensyn_sem_small i think? *)

datatype s_error =
  Exec childpath
  | BadPath
  | NoFuel
  | Done
  | Crash
  | Halted (* halted = too much fuel *)

fun s_error_safe :: "s_error \<Rightarrow> bool" where
"s_error_safe (Exec _) = True"
| "s_error_safe Done = True"
| "s_error_safe _ = False"

(* we also need to be able to separate sub-syntax from entire tree *)


record ('syn, 'mstate) sem' =
  s_sem :: "'syn \<Rightarrow> 'mstate \<Rightarrow> 'mstate"

(* TODO: list updates *)
record ('syn, 'mstate) sem = "('syn, 'mstate) sem'" +
  s_cont :: "'mstate \<Rightarrow> 'syn gensyn list"

(* OK, for CPS approach we need to have each control-flow state
   be able to manipulate and return a list of targets *)


(* where is path update *)

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
  (case s_cont gs m of
    [] \<Rightarrow> None
    | ((G x l)#tt) \<Rightarrow> Some (s_sem gs x m))"

(* Another option: leave an "open port" in all control flow modules?

see if this will break any typeclasses...

*)

(* maybe use a relational small-step, relate it to the executable one? *)
fun sem_exec ::
  "('x, 'mstate) sem \<Rightarrow>
   nat \<Rightarrow>
   'mstate \<Rightarrow>
   ('mstate * s_error)" where
"sem_exec gs 0 m = 
  (case s_cont gs m of
    [] \<Rightarrow> (m, Done)
    | _ \<Rightarrow> (m, NoFuel))"
| "sem_exec gs (Suc n) m =
   (case s_cont gs m of
    [] \<Rightarrow> (m, Halted)
    | ((G x l)#tt) \<Rightarrow> sem_exec gs n (s_sem gs x m))"

inductive sem_step_p ::
  "('x, 'mstate) sem \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool"
  where
"\<And> gs (m :: 'mstate) (m' :: 'mstate) x l  tt .
 s_cont gs m = ((G x l)#tt) \<Longrightarrow> 
 s_sem gs x m = m' \<Longrightarrow>
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
  by(auto simp add: sem_step_def split: s_error.splits list.splits option.splits intro: sem_step_p.intros)

lemma sem_step_exec1 :
  assumes H : "sem_step gs m = Some m'"
  shows "\<exists> s . (sem_exec gs 1 m = (m', s))" using H
  by(auto simp add: sem_step_def  split:list.splits option.splits)

lemma sem_exec1_step :
  assumes H : "(sem_exec gs 1 m = (m', s))"
  assumes H' : "s_error_safe s"
  shows "sem_step gs m = Some m'" using assms
  by(auto simp add: sem_step_def split:option.splits list.splits)

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

(* have the state contain a delta to the continuation list?
   that is, a new prefix to prepend *)
definition imm_safe :: "('x, 'mstate) sem \<Rightarrow> 'mstate \<Rightarrow> bool" where
"imm_safe gs m \<equiv>
 ((s_cont gs m = []) \<or>
  (\<exists> m' . sem_step_p gs m m'))"

definition safe :: "('x, 'mstate) sem \<Rightarrow> 'mstate \<Rightarrow> bool" where
"safe gs m \<equiv>
  (\<forall> m' . sem_exec_p gs m m' \<longrightarrow> imm_safe gs m')"

(* TODO: syntax *)
definition guarded :: "('x, 'mstate) sem \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> 'x gensyn list \<Rightarrow> bool"
("|_| {_} _")
 where
"guarded gs P c =
  (\<forall> m . P m \<longrightarrow> s_cont gs m = c \<longrightarrow> safe gs m)"

definition HT :: "('x, 'mstate) sem \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> 'x gensyn list \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> bool" 
  ("|_| {-_-} _ {-_-}")
  where
"HT gs P c Q =
  (\<forall> c' .  |gs| {Q} (c') \<longrightarrow> |gs| {P} (c @ c'))"

(* maybe there is another way we can achieve some kind of separation of concerns between control/continuation
   and the rest of the state... 
   heavy(ier) weight approach: just use lens (identity lifting)
   or just directly require that it be a product
    - continuation list
    - result continuation change (does this even need to be separate?)
    - other state
*)

lemma HConseq :
  assumes H : "|gs| {- P' -} c {-Q'-}"
  assumes H' : "\<And> st . P st \<Longrightarrow> P' st"
  assumes H'' : "\<And> st . Q' st \<Longrightarrow> Q st"
  shows "|gs| {-P-} c {-Q-}" using H

  unfolding HT_def guarded_def safe_def imm_safe_def
  apply(auto)
   apply(drule_tac x = "c'" in spec) 
  apply(auto)
   apply(drule_tac H'')
  apply(auto)

  apply(drule_tac H')
  apply(rotate_tac -1)
  apply(drule_tac x = "m" in spec) apply(auto)
  done

(* this is not true - need to further constrain that we halt after the first step,
   or do something else to strengthen the assumptions *)

(* need to say something about how the continuation changes when
   we execute the first instruction
*)

(* issue might have to do with how we represent errors.
   returning empty list vs returning None
   we could just not distinguish these cases.
*)
(*
  or. another thought.
*)
lemma HStep : 
  assumes H : "(! sem ) % {{P}} c {{Q}}"
  assumes Hgs : "s_sem gs = sem"
  shows "|gs| {-P-} [G c l] {-Q-}" using H Hgs 
  unfolding HT_def guarded_def safe_def imm_safe_def semprop2_def VT_def 
  apply(auto)
  apply(simp add: sem_exec_p_def)

  apply(drule_tac x = m in spec) apply(auto)
  apply(drule_tac x = "(s_sem gs c m) " in spec) apply(auto)
   apply(case_tac "sem_step gs m'")
    apply(simp add: sem_step_def )
    apply(case_tac "s_cont gs m'")
     apply(auto)
  apply(drule_tac sem_step_sem_step_p)
   apply(auto)

   apply(case_tac "sem_step gs m'")
    apply(simp add: sem_step_def )
    apply(case_tac "s_cont gs m'")
     apply(auto)
  apply(drule_tac sem_step_sem_step_p)
  apply(auto)
  done


end