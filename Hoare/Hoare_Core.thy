theory Hoare_Core imports 
 "../Gensyn" "../Gensyn_Descend" "../Mergeable/Mergeable"
 "../Lifting/LiftUtils" "../Lifting/LiftInstances" "../Lifting/LangCompFull"
 "../Relpath" (*"../Semantics/Gensyn_Sem_Small"*) "Hoare"
begin


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


type_synonym ('full, 'mstate) control =
  "('full gensyn list md_triv option md_prio * String.literal md_triv option md_prio * 'mstate)"

definition payload :: "('full, 'mstate) control \<Rightarrow> 'mstate" where
"payload c =
  (case c of
    (_, _, m) \<Rightarrow> m)"

declare payload_def [simp add]

record ('syn, 'mstate) sem' =
  s_sem :: "'syn \<Rightarrow> 'mstate \<Rightarrow> 'mstate"

(* TODO: this should be an entire lifting (at least a weak lifting.) *)
(*
record ('syn, 'full, 'mstate) sem = "('syn, 'mstate) sem'" +
  s_cont :: "'mstate \<Rightarrow> 'full gensyn list"
*)

(*
record ('syn, 'full, 'mstate) sem = "('syn, 'mstate) sem'" +
  s_l :: "('syn, 'full gensyn list, 'mstate) lifting"
*)

record ('syn, 'full, 'mstate) sem = 
  s_sem :: "'syn \<Rightarrow> ('full, 'mstate) control \<Rightarrow> ('full, 'mstate) control"


type_synonym 'x orerror =
  "('x + String.literal)"

definition s_cont :: "('full, 'mstate) control \<Rightarrow> ('full gensyn list orerror)" where
"s_cont m \<equiv>
  (case m of
    ((mdp _ (Some (mdt x))), (mdp _ None), _) \<Rightarrow> Inl x
    | ((mdp _ None), _, _) \<Rightarrow> Inr (STR ''Hit bottom in continuation field'') 
    | ((mdp _ _), (mdp _ (Some (mdt msg))), _) \<Rightarrow> Inr msg)"

(*
definition close :: "('syn, 'full, 'mstate) sem \<Rightarrow> ('full \<Rightarrow> 'syn) \<Rightarrow> ('full, 'full, 'mstate) sem" where
"close s f =
  \<lparr> s_sem = (s_sem s o f)
  , s_cont = s_cont s \<rparr>"
*)
(* "closed" sem
   we obtain this when our "full" syntax becomes the same as
   our "individual syntax"
*)
type_synonym ('syn, 'mstate) semc = "('syn, 'syn, 'mstate) sem"

record ('syn, 'full, 'mstate) semt = "('syn, 'full, 'mstate) sem" +
  s_transl :: "'full \<Rightarrow> 'syn"

definition sem_step ::
  "('syn, 'mstate) semc \<Rightarrow>
   ('syn, 'mstate) control \<Rightarrow>
   ('syn, 'mstate) control orerror" where
"sem_step gs m =
  (case s_cont m of
    Inr msg \<Rightarrow> Inr msg
    | Inl [] \<Rightarrow> Inr (STR ''Halted'')
    | Inl ((G x l)#tt) \<Rightarrow> Inl (s_sem gs x m))"

fun sem_exec ::
  "('syn, 'mstate) semc \<Rightarrow>
   nat \<Rightarrow>
   ('syn, 'mstate) control \<Rightarrow>
   (('syn, 'mstate) control orerror)" where
"sem_exec gs 0 m = 
  (case s_cont m of
    Inr msg \<Rightarrow> Inr msg
    | Inl [] \<Rightarrow> Inl m
    | _ \<Rightarrow> Inr (STR ''No fuel left''))"
| "sem_exec gs (Suc n) m =
   (case s_cont m of
    Inr msg \<Rightarrow> Inr msg
    | Inl [] \<Rightarrow> Inr (STR ''Excess fuel'')
    | Inl ((G x l)#tt) \<Rightarrow> sem_exec gs n (s_sem gs x m))"

inductive sem_step_p ::
  "('syn, 'mstate) semc  \<Rightarrow> ('syn, 'mstate) control \<Rightarrow> ('syn, 'mstate) control \<Rightarrow> bool"
  where
"\<And> gs m m' x l  tt .
 s_cont m = Inl ((G x l)#tt) \<Longrightarrow> 
 s_sem gs x m = m' \<Longrightarrow>
 sem_step_p gs m m'"

definition sem_exec_p ::
  "('syn, 'mstate) semc  \<Rightarrow> ('syn, 'mstate) control \<Rightarrow> ('syn, 'mstate) control \<Rightarrow> bool" where
"sem_exec_p gs \<equiv>
  (rtranclp (sem_step_p gs))"

declare sem_exec_p_def [simp add]

lemma sem_step_p_sem_step :
  assumes H : "sem_step_p gs m m'"
  shows "sem_step gs m = Inl m'" using H
proof(cases rule: sem_step_p.cases)
  case (1 sub)
  then show ?thesis 
    by(auto simp add: sem_step_def)
qed

lemma sem_step_sem_step_p :
  assumes H : "sem_step gs m = Inl m'"
  shows "sem_step_p gs m m'" using H
  by(auto simp add: sem_step_def split: s_error.splits list.splits option.splits sum.splits intro: sem_step_p.intros)


lemma sem_step_p_eq :
  "(sem_step_p gs m m') = (sem_step gs m = Inl m') "
  using sem_step_p_sem_step[of gs m m'] sem_step_sem_step_p[of gs m m']
  by(auto)

(*
lemma sem_step_exec1 :
  assumes H : "sem_step gs m = Inl m'"
  shows "\<exists> s . (sem_exec gs 1 m = Inl m')" using H
  byy(auto simp add: sem_step_def  split:list.splits option.splits sum.splits)

lemma sem_exec1_step :
  assumes H : "(sem_exec gs 1 m = (m', s))"
  assumes H' : "s_error_safe s"
  shows "sem_step gs m = Some m'" using assms
  by(auto simp add: sem_step_def split:option.splits list.splits)
*)

abbreviation spred :: "('c \<Rightarrow> bool) \<Rightarrow> ('a * 'b * 'c) \<Rightarrow> bool" ("\<star>_")
  where
"\<star>P \<equiv> P o snd o snd"

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

(* lemma for reasoning about compound executions *)
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

(* lemma for reasoning about executions which cannot step  *)
lemma rtranclp_nostep :
  assumes H0 : "determ R"
  assumes H : "R\<^sup>*\<^sup>* x1 x2"
  assumes H1 : "\<And> x1' . R x1 x1' \<Longrightarrow> False"
  shows "x1 = x2" using H H0 H1
proof(induction  rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step y z)

  have Xeq : "x1 = y"
    using step.IH[OF step.prems(1) step.prems(2), of id]
    by auto

  show ?case using step.hyps step.prems(2) unfolding Xeq
    by auto
qed

lemma rtranclp_paths_step :
  assumes H0 : "determ R"
  assumes H1 : "R\<^sup>*\<^sup>* x1 y"
  assumes H2 : "R x1 x2"
  shows "(x1 = y \<or> R\<^sup>*\<^sup>* x2 y)" using H1 H2
proof(induction arbitrary: x2 rule:rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step nxt last)

  have Opts : "x1 = nxt \<or> R\<^sup>*\<^sup>* x2 nxt"
    using step.IH[OF step.prems(1)] by auto

  then show ?case
  proof(cases "x1 = nxt")
    case True

    then have X1alt : "R x1 last" 
      using step.hyps by auto

    then have X2alt : "x2 = last"
      using determE[OF H0 X1alt step.prems(1)]
      by auto

    hence "R\<^sup>*\<^sup>* x2 last"
      by auto

    thus ?thesis by auto
  next
    case False

    then have False' : "R\<^sup>*\<^sup>* x2 nxt" using Opts by auto

    show ?thesis using rtranclp.intros(2)[OF False' step.hyps(2)]
      by auto
  qed
qed


lemma rtranclp_paths :
  assumes H0 : "determ R"
  assumes H1 : "R\<^sup>*\<^sup>* x y1"
  assumes H2 : "R\<^sup>*\<^sup>* x y2"
  shows
    "(R\<^sup>*\<^sup>* y2 y1) \<or>
     (R\<^sup>*\<^sup>* y1 y2)" using H1 H2
proof(induction arbitrary: y2 rule:rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step nxt last)

  have Alts : "R\<^sup>*\<^sup>* y2 nxt \<or> R\<^sup>*\<^sup>* nxt y2"
    using step.IH[OF step.prems(1)] by auto

  show ?case 
  proof(cases "R\<^sup>*\<^sup>* y2 nxt")
    case True

    then have "R\<^sup>*\<^sup>* y2 last"
      using rtranclp.intros(2)[OF True step.hyps(2)] by auto

    then show ?thesis by auto
  next
    case False

    then have False' : "R\<^sup>*\<^sup>* nxt y2" using Alts by auto

    have Alts' : "nxt = y2 \<or> R\<^sup>*\<^sup>* last y2"
      using rtranclp_paths_step[OF H0 False' step.hyps(2)]
      by auto

    show ?thesis
    proof(cases "nxt = y2")
      case True

      then have "R\<^sup>*\<^sup>* y2 last" using step.hyps(2) by auto

      then show ?thesis by auto
    next
      case False

      hence False'' : "R\<^sup>*\<^sup>* last y2" using Alts' by auto

      then show ?thesis by auto
    qed
  qed
qed


end