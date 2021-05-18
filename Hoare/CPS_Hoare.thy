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

(* TODO: this should be an entire lifting (at least a weak lifting.) *)
record ('syn, 'full, 'mstate) sem = "('syn, 'mstate) sem'" +
  s_cont :: "'mstate \<Rightarrow> 'full gensyn list"

definition close :: "('syn, 'full, 'mstate) sem \<Rightarrow> ('full \<Rightarrow> 'syn) \<Rightarrow> ('full, 'full, 'mstate) sem" where
"close s f =
  \<lparr> s_sem = (s_sem s o f)
  , s_cont = s_cont s \<rparr>"

(* "closed" sem
   we obtain this when our "full" syntax becomes the same as
   our "individual syntax"
*)
type_synonym ('syn, 'mstate) semc = "('syn, 'syn, 'mstate) sem"

record ('syn, 'full, 'mstate) semt = "('syn, 'full, 'mstate) sem" +
  s_transl :: "'full \<Rightarrow> 'syn"

definition s_semt :: "('syn, 'full, 'mstate) semt \<Rightarrow> 'full \<Rightarrow> 'mstate \<Rightarrow> 'mstate" where
"s_semt s = s_sem s o s_transl s"

definition sem_step ::
  "('syn, 'mstate) semc \<Rightarrow>
   'mstate \<Rightarrow>
   ('mstate option)" where
"sem_step gs m =
  (case s_cont gs m of
    [] \<Rightarrow> None
    | ((G x l)#tt) \<Rightarrow> Some (s_sem gs x m))"

(* Another option: leave an "open port" in all control flow modules?

see if this will break any typeclasses...

*)

fun sem_exec ::
  "('x, 'mstate) semc \<Rightarrow>
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
  "('x, 'mstate) semc \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool"
  where
"\<And> gs (m :: 'mstate) (m' :: 'mstate) x l  tt .
 s_cont gs m = ((G x l)#tt) \<Longrightarrow> 
 s_sem gs x m = m' \<Longrightarrow>
 sem_step_p gs m m'"

definition sem_exec_p ::
  "('x, 'mstate) semc \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool" where
"sem_exec_p gs \<equiv>
  (rtranclp (sem_step_p gs))"

declare sem_exec_p_def [simp add]

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

lemma sem_step_p_eq :
  "(sem_step_p gs m m') = (sem_step gs m = Some m') "
  using sem_step_p_sem_step sem_step_sem_step_p
  by auto

lemma sem_step_exec1 :
  assumes H : "sem_step gs m = Some m'"
  shows "\<exists> s . (sem_exec gs 1 m = (m', s))" using H
  by(auto simp add: sem_step_def  split:list.splits option.splits)

lemma sem_exec1_step :
  assumes H : "(sem_exec gs 1 m = (m', s))"
  assumes H' : "s_error_safe s"
  shows "sem_step gs m = Some m'" using assms
  by(auto simp add: sem_step_def split:option.splits list.splits)

(* have the state contain a delta to the continuation list?
   that is, a new prefix to prepend *)
definition imm_safe :: "('x, 'mstate) semc \<Rightarrow> 'mstate \<Rightarrow> bool" where
"imm_safe gs m \<equiv>
 ((s_cont gs m = []) \<or>
  (\<exists> m' . sem_step_p gs m m'))"

lemma imm_safeI_Done :
  assumes H : "s_cont gs m = []"
  shows "imm_safe gs m" using H
  unfolding imm_safe_def by auto

lemma imm_safeI_Step :
  assumes H : "sem_step_p gs m m'"
  shows "imm_safe gs m" using H
  unfolding imm_safe_def by auto

lemma imm_safeD :
  assumes H : "imm_safe gs m"
  shows "((s_cont gs m = []) \<or>
  (\<exists> m' . sem_step_p gs m m'))" using H
  unfolding imm_safe_def by auto


definition safe :: "('x, 'mstate) semc \<Rightarrow> 'mstate \<Rightarrow> bool" where
"safe gs m \<equiv>
  (\<forall> m' . sem_exec_p gs m m' \<longrightarrow> imm_safe gs m')"

lemma safeI [intro]:
  assumes H : "\<And> m' . sem_exec_p gs m m' \<Longrightarrow> imm_safe gs m'"
  shows "safe gs m" using H unfolding safe_def
  by auto

lemma safeD :
  assumes H : "safe gs m"
  assumes Hx : "sem_exec_p gs m m'"
  shows "imm_safe gs m'" using H Hx
  unfolding safe_def by auto

(* TODO: syntax *)
definition guarded :: "('x, 'mstate) semc \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> 'x gensyn list \<Rightarrow> bool"
("|_| {_} _")
 where
"guarded gs P c =
  (\<forall> m . P m \<longrightarrow> s_cont gs m = c \<longrightarrow> safe gs m)"

lemma guardedI [intro] :
  assumes H : "\<And> m . P m \<Longrightarrow> s_cont gs m = c \<Longrightarrow> safe gs m"
  shows "guarded gs P c" using H
  unfolding guarded_def by auto

lemma guardedD :
  assumes H : "guarded gs P c"
  assumes HP : "P m"
  assumes Hcont : "s_cont gs m = c"
  shows "safe gs m" using assms
  unfolding guarded_def by auto

definition HT :: "('x, 'mstate) semc \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> 'x gensyn list \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> bool" 
  ("|_| {-_-} _ {-_-}")
  where
"HT gs P c Q =
  (\<forall> c' .  |gs| {Q} (c') \<longrightarrow> |gs| {P} (c @ c'))"

lemma HTI [intro] :
  assumes H : "\<And> c' . |gs| {Q} (c') \<Longrightarrow> |gs| {P} (c @ c')"
  shows "HT gs P c Q" using H unfolding HT_def
  by auto

lemma HTE [elim]:
  assumes H : "HT gs P c Q"
  assumes H' : "|gs| {Q} c'"
  shows "|gs| {P} (c@c')" using assms
  unfolding HT_def
  by auto

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
lemma HStep : 
  assumes H : "(! sem ) % {{P}} c {{Q}}"
  assumes Hgs : "s_sem gs = sem"
  shows "|gs| {-P-} [G c l] {-Q-}" using H Hgs 
  unfolding HT_def guarded_def safe_def imm_safe_def semprop2_def VT_def 
  apply(auto)

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

(* sequencing lemma *)
lemma HCat :
  assumes H : "|gs| {- P1 -} c1 {- P2 -}"
  assumes H' : "|gs| {- P2 -} c2 {- P3 -}"
  shows "|gs| {- P1 -} c1 @ c2 {- P3 -}"
proof(rule HTI)
  fix c'
  assume HP3 : "|gs| {P3} c'"

  have P2_cont : "|gs| {P2} c2 @ c'"
    using HTE[OF H' HP3]
    by auto

  show "|gs| {P1} (c1 @ c2) @ c'"
    using HTE[OF H P2_cont]
    unfolding append_assoc
    by auto
qed

definition determ :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"determ R \<equiv>
  (\<forall> a b b' . R a b \<longrightarrow> R a b' \<longrightarrow> b = b')"

lemma determI [intro] :
  assumes "\<And> a b b' . R a b \<Longrightarrow> R a b' \<Longrightarrow> b = b'"
  shows "determ R" using assms unfolding determ_def by auto

lemma determE :
  assumes H : "determ R"
  assumes H1 : "R a b"
  assumes H2 : "R a b'"
  shows "b = b'" using assms
  unfolding determ_def
  by auto

lemma sem_step_determ :
  "determ (sem_step_p gs)"
proof
  fix a b b'
  assume H1 : "sem_step_p gs a b"
  assume H2 : "sem_step_p gs a b'"

  show "b = b'" using H1 H2 unfolding sem_step_p_eq by auto
qed

(* helpful lemma for reasoning about compound executions *)
lemma rtranclp_bisect1 :
  assumes H0 : "determ R"
  assumes H : "R\<^sup>*\<^sup>* xi xp"
  assumes H1 : "R xi x1"
  assumes H2 : "R xp xf"
  shows "R\<^sup>*\<^sup>* x1 xf" using H H0 H1 H2
proof(induction arbitrary: x1 xf rule: rtranclp_induct)
  case base

  have Eq : "x1 = xf" using determE[OF H0 base(2) base(3)] by auto

  then show ?case using base by auto
next
  case (step y z)

  have X1z : "R\<^sup>*\<^sup>* x1 z" using step.IH[OF step.prems(1) step.prems(2) step.hyps(2)]
    by auto

  show ?case using rtranclp.intros(2)[OF X1z step.prems(3)] by auto
qed


(*
  Restriction requiring that predicates cannot look at continuation
*)

(*
definition blind :: "('x, 'mstate) semc \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> bool" where
"blind gs P =
  (\<forall> x y . gs_cont x = gs_cont
*)

definition blind' :: "('x, 'mstate) semc \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> bool" where
"blind' gs P =
  (\<forall> c x . P x \<longrightarrow> (\<exists> x' . s_cont gs x' = c \<and> P x'))"

lemma blind'E : 
  assumes H : "blind' gs P"
  assumes HP : "P x"
  shows "\<exists> x' . s_cont gs x' = c \<and> P x'" using assms
  unfolding blind'_def
  by auto

lemma blind'I [intro] :
  assumes H : "(\<And> c x . P x \<Longrightarrow> (\<exists> x' . s_cont gs x' = c \<and> P x'))"
  shows "blind' gs P" using H unfolding blind'_def by auto

end