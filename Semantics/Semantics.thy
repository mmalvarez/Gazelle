theory Semantics imports "../Syntax/Gensyn" "../Mergeable/Wrappers"
begin

(*
 * A small-step operational semantics for Gazelle.
 * This semantics uses the gensyn datatype, and is parameterized by the semantics
 * giving a denotation corresponding to executing the commands contained in the input program
 * (of type gensyn)
 *
 * The primary thing handled here is control: that is, when inspecting a program state,
 * how do we decide which command to execute next? Once we have determined this,
 * we can call the semantics for that command to get a new state (corresponding to one
 * step of execution); then, if appropriate, repeat.
 *
 * Additionally, we push all possibility for nontermination out to this level. By requiring that
 * the semantics of individual commands (that is, the semantics of _taking a single step_
 * at a command) are terminating, we can allow the user to specify the semantics
 * denotationally as pure functional programs in Isabelle, without any complications.
 *)

(* 'mstate augmented with control information used by the semantics *)
type_synonym ('full, 'mstate) control =
  "('full gensyn list md_triv option md_prio * String.literal option md_triv option md_prio * 'mstate)"

(* TODO: having separate 'syn and 'full type parameters may be unnecessary *)
type_synonym ('syn, 'full, 'mstate) sem = 
  "'syn \<Rightarrow> ('full, 'mstate) control \<Rightarrow> ('full, 'mstate) control"

type_synonym 'x orerror =
  "('x + String.literal)"

(* semc = "closed" sem: we force 'syn and 'full to be equal  *)
type_synonym ('syn, 'mstate) semc = "('syn, 'syn, 'mstate) sem"

definition payload :: "('full, 'mstate) control \<Rightarrow> 'mstate" where
"payload c =
  (case c of
    (_, _, m) \<Rightarrow> m)"

declare payload_def [simp add]

(*
definition cont :: "('full, 'mstate) control \<Rightarrow> ('full gensyn list orerror)" where
"cont m \<equiv>
  (case m of
    ((mdp _ (Some (mdt x))), (mdp _ (Some (mdt (STR '''')))), _) \<Rightarrow> Inl x
    | ((mdp _ None), _, _) \<Rightarrow> Inr (STR ''Hit bottom in continuation field'') 
    | ((mdp _ _), (mdp _ None), _) \<Rightarrow> Inr (STR ''Hit bottom in message field'') 
    | ((mdp _ _), (mdp _ (Some (mdt msg))), _) \<Rightarrow> Inr msg)"
*)

definition cont :: "('full, 'mstate) control \<Rightarrow> ('full gensyn list orerror)" where
"cont m \<equiv>
  (case m of
    ((mdp _ (Some (mdt x))), (mdp _ (Some (mdt msg))), _) \<Rightarrow> 
      (case msg of
        None \<Rightarrow> Inl x
        | Some msg \<Rightarrow> Inr msg)
    | ((mdp _ None), _, _) \<Rightarrow> Inr (STR ''Hit bottom in continuation field'') 
    | ((mdp _ _), (mdp _ None), _) \<Rightarrow> Inr (STR ''Hit bottom in message field''))"


(* Small-step semantics *)
definition sem_step ::
  "('syn, 'mstate) semc \<Rightarrow>
   ('syn, 'mstate) control \<Rightarrow>
   ('syn, 'mstate) control orerror" where
"sem_step gs m =
  (case cont m of
    Inr msg \<Rightarrow> Inr msg
    | Inl [] \<Rightarrow> Inr (STR ''Halted'')
    | Inl ((G x l)#tt) \<Rightarrow> Inl (gs x m))"

(* Executable version of interpreter as a series of small-steps *)
(* TODO: show correspondence between this and sem_exec_p *)
fun sem_exec ::
  "('syn, 'mstate) semc \<Rightarrow>
   nat \<Rightarrow>
   ('syn, 'mstate) control \<Rightarrow>
   (('syn, 'mstate) control orerror)" where
"sem_exec gs 0 m = 
  (case cont m of
    Inr msg \<Rightarrow> Inr msg
    | Inl [] \<Rightarrow> Inl m
    | _ \<Rightarrow> Inr (STR ''No fuel left''))"
| "sem_exec gs (Suc n) m =
   (case cont m of
    Inr msg \<Rightarrow> Inr msg
    | Inl [] \<Rightarrow> Inr (STR ''Excess fuel'')
    | Inl ((G x l)#tt) \<Rightarrow> sem_exec gs n (gs x m))"

(* Easier-to-use interpreter, does not require exact fuel.
 * TODO: show correspondence between this and sem_exec *)
fun sem_run :: "('syn, 'mstate) semc \<Rightarrow> nat \<Rightarrow>
('syn, 'mstate) control \<Rightarrow>
   (('syn, 'mstate) control orerror)" where
"sem_run gs 0 m =
  (case cont m of
    Inr msg \<Rightarrow> Inr msg
    | Inl [] \<Rightarrow> Inl m
    | _ \<Rightarrow> Inl m)"
| "sem_run gs (Suc n) m =
   (case cont m of
    Inr msg \<Rightarrow> Inr msg
    | Inl [] \<Rightarrow> Inl m
    | Inl ((G x l)#tt) \<Rightarrow> sem_run gs n (gs x m))"

inductive sem_step_p ::
  "('syn, 'mstate) semc  \<Rightarrow> ('syn, 'mstate) control \<Rightarrow> ('syn, 'mstate) control \<Rightarrow> bool"
  where
"\<And> gs m x l  tt .
 cont m = Inl ((G x l)#tt) \<Longrightarrow> 
 sem_step_p gs m (gs x m)"

(* We can express sem_exec equivalently as a reflexive-transitive closure of taking a step *)
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
  by(auto simp add: sem_step_def split: list.splits option.splits sum.splits intro: sem_step_p.intros)

lemma sem_step_p_eq :
  "(sem_step_p gs m m') = (sem_step gs m = Inl m') "
  using sem_step_p_sem_step[of gs m m'] sem_step_sem_step_p[of gs m m']
  by(auto)

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

(* An alternate execution relation with an explicit step-count (hence the "c")
 * We then prove it equivalent to sem_exec_p *)
inductive sem_exec_c_p ::
  "('syn, 'mstate) semc  \<Rightarrow> ('syn, 'mstate) control \<Rightarrow> nat \<Rightarrow> ('syn, 'mstate) control \<Rightarrow> bool"
  for gs :: "('syn, 'mstate) semc" 
  where
Excp_0 :"sem_exec_c_p gs m 0 m"
| Excp_Suc :
  "sem_step_p gs m1 m2 \<Longrightarrow>
   sem_exec_c_p gs m2 n m3 \<Longrightarrow>
   sem_exec_c_p gs m1 (Suc n) m3"

lemma exec_c_p_imp_exec_p :
  assumes H : "sem_exec_c_p gs m n m'"
  shows "sem_exec_p gs m m'" using H
proof(induction rule: sem_exec_c_p.induct)
  case (Excp_0 m)
  then show ?case unfolding sem_exec_p_def by auto
next
  case (Excp_Suc m1 m2 n m3)
  then show ?case by auto
qed

lemma Excp_Suc_gen :
  assumes H1 : "sem_exec_c_p gs m1 n1 m2"
  assumes H2 : "sem_exec_c_p gs m2 n2 m3"
  shows "sem_exec_c_p gs m1 (n1 + n2) m3" using assms
proof(induction arbitrary: n2 m3 rule: sem_exec_c_p.induct)
  case (Excp_0 m)
  then show ?case by auto
next
  case Xsuc : (Excp_Suc m1' m2' n' m3')
  show ?case 
    using Excp_Suc[OF Xsuc.hyps(1) Xsuc.IH[OF Xsuc.prems(1)]]
    by auto
qed

lemma Excp_1 : 
  assumes H : "sem_step_p gs m1 m2"
  shows "sem_exec_c_p gs m1 1 m2" using H
  by(auto intro: sem_exec_c_p.intros)

lemma exec_p_imp_exec_c_p :
  assumes H : "sem_exec_p gs m m'"
  shows "\<exists> n . sem_exec_c_p gs m n m'" using H
  unfolding sem_exec_p_def
proof(induction rule:rtranclp_induct)
  case base

  have "sem_exec_c_p gs m 0 m" using Excp_0[of gs m] by auto

  then show ?case by auto
next
  case (step y z)

  then obtain n where N: "sem_exec_c_p gs m n y"
    by auto

  have Nstep : "sem_exec_c_p gs y 1 z" using Excp_1[OF step.hyps(2)]
    by auto

  have "sem_exec_c_p gs m (n + 1) z"
    using Excp_Suc_gen[OF N Nstep] by auto

  thus ?case by auto
qed

(* divergence *)
definition diverges :: "('syn, 'mstate) semc \<Rightarrow> ('syn, 'mstate) control \<Rightarrow> bool" where
"diverges gs st =
  (\<forall> st' . sem_exec_p gs st st' \<longrightarrow> (\<exists> st'' . sem_step_p gs st' st''))"

lemma divergesI :
  assumes H : "\<And> st' . sem_exec_p gs st st' \<Longrightarrow> (\<exists> st'' . sem_step_p gs st' st'')"
  shows "diverges gs st" using H unfolding diverges_def by auto

lemma divergesD :
  assumes H : "diverges gs st"
  assumes Hst : "sem_exec_p gs st st'"
  shows "\<exists> st'' . sem_step_p gs st' st''"
    using assms unfolding diverges_def by blast

end