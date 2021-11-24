theory Hoare imports 
 "../Syntax/Gensyn" "../Syntax/Gensyn_Descend" "../Mergeable/Mergeable"
 "../Semantics/Semantics" "../Semantics/Semantics_Facts"
begin

(* A simple implementation of primitives for a (sound) partial-correctness 
 * Hoare logic on top of the general Gazelle semantics.
 * This model of Hoare logic is based on the CPS-flavored version described in
 * _Program Logics for Certified Compilers_ and _Separation Logic for Small-Step Cminor_
 *)

definition imm_safe :: "('syn, 'mstate) semc \<Rightarrow> ('syn, 'mstate) control  \<Rightarrow> bool" where
"imm_safe gs m \<equiv>
 ((cont m = Inl []) \<or>
  (\<exists> m' . sem_step_p gs m m'))"

lemma imm_safeI_Done :
  assumes H : "cont m = Inl []"
  shows "imm_safe gs m" using H
  unfolding imm_safe_def by auto

lemma imm_safeI_Step :
  assumes H : "sem_step_p gs m m'"
  shows "imm_safe gs m" using H
  unfolding imm_safe_def
  by(cases m'; auto)

lemma imm_safeD :
  assumes H : "imm_safe gs m"
  shows "((cont m = Inl []) \<or>
  (\<exists> m' . sem_step_p gs m m'))" using H
  unfolding imm_safe_def by (auto)

(* Safe means we terminate or diverge (partial correctness) *)
definition safe :: "('syn, 'mstate) semc \<Rightarrow> ('syn, 'mstate) control \<Rightarrow> bool" where
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
  unfolding safe_def by blast

(* Guarded: if we start in a state satisfying P, we are safe *)
definition guarded :: "('syn, ('mstate :: Okay)) semc \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> 'syn gensyn list \<Rightarrow> bool"
("|_| {_} _" [200, 202, 204])
 where
"guarded gs P c =
  (\<forall> m . m \<in> ok_S \<longrightarrow> P (payload m) \<longrightarrow> cont m = Inl c \<longrightarrow> safe gs m)"

lemma guardedI [intro] :
  assumes H : "\<And> m . m \<in> ok_S \<Longrightarrow> P (payload m) \<Longrightarrow> cont m = Inl c \<Longrightarrow> safe gs m"
  shows "guarded gs P c" using H
  unfolding guarded_def
  by auto

lemma guardedD :
  assumes H : "guarded gs P c"
  assumes HOk : "m \<in> ok_S"
  assumes HP : "P (payload m)"
  assumes Hcont : "cont m = Inl c"
  shows "safe gs m" using assms
  unfolding guarded_def by blast

(* Hoare triple definition:
 * For any tail c' that is safe under condition Q (the postcondition of the triple),
 * the program c followed by the tail c' will be safe under P (the precondition)
 *)
definition HT :: "('syn, ('mstate :: Okay)) semc \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> 'syn gensyn list \<Rightarrow> ('mstate \<Rightarrow> bool)\<Rightarrow> bool" 
  ("|_| {-_-} _ {-_-}" [206, 208, 210])
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

lemma HConseq :
  assumes H : "|gs| {- P' -} c {-Q'-}"
  assumes H' : "\<And> st . P st \<Longrightarrow> P' st"
  assumes H'' : "\<And> st . Q' st \<Longrightarrow> Q st"
  shows "|gs| {-P-} c {-Q-}"
proof(rule HTI)
  fix c'
  assume Exec : "|gs| {Q} c'"

  then have Exec' : "|gs| {Q'} c'"
    unfolding guarded_def using H'' by blast

  then have Exec'' :"|gs| {P'} (c@c')"
    using HTE[OF H Exec'] by auto

  then show "|gs| {P} (c @ c')"
    unfolding guarded_def using H' by blast
qed

(* Lifting for non-control, single-step instructions *)
(* TODO: this proof needs to be fixed *)
(*
lemma HStep : 
  assumes H : "(! sem ) % {{P o payload}} c {{Q o payload}}"
  assumes Hgs : "s_sem gs = sem"
  shows "|gs| {-P-} [G c l] {-Q-}" 
proof(rule HTI)
  fix c'
  assume Exec : "|gs| {Q} c'"

  show "|gs| {P} [G c l] @ c'"
  proof(rule guardedI)
    fix m :: "('a, 'b) control"

    assume P : "P (payload m)"
    obtain ms mm mc where M: "m = (mc, mm, ms)" and P' : "P ms"
      using P by (cases m; auto)

    assume Cont : "s_cont m = Inl ([G c l] @ c')"

    have Q: "Q (payload (s_sem gs c m))"
      using H P M unfolding semprop2_def VT_def Hgs
      by(auto)

    have "s_cont (sem.s_sem gs c m) = Inl c' " using Hgs
      apply(auto simp add: s_cont_def split: prod.splits md_prio.splits option.splits md_triv.splits)

(* *)
(* idea: sem will only modify the payload. *)
    show "safe gs m" using guardedD[OF Exec Q]

    show "safe gs m"
    proof(rule safeI)
      fix m'
      assume Exec' : "sem_exec_p gs m m'"
      show "imm_safe gs m'"

      proof(cases "s_cont m'")
        case (Inr bad)
        then have False using Cont by auto
        case Nil
        then show ?thesis unfolding imm_safe_def by auto
      next
        case (Cons a list)
        then show ?thesis using Exec' unfolding sem_exec_p_def imm_safe_def sem_step_p_eq sem_step_def
          by(cases m; auto)
      qed
    qed
  qed
qed
*)

(* sequencing lemma *)
lemma HCat :
  assumes H : "|gs| {- P1 -} c1 {- P2 -}"
  assumes H' : "|gs| {- P2 -} c2 {- P3 -}"
  shows "|gs| {- P1 -} (c1 @ c2) {- P3 -}"
proof(rule HTI)
  fix c'
  assume HP3 : "|gs| {P3} c'"

  have P2_cont : "|gs| {P2} (c2 @ c')"
    using HTE[OF H' HP3]
    by auto

  show "|gs| {P1} ((c1 @ c2) @ c')"
    using HTE[OF H P2_cont]
    unfolding append_assoc
    by auto
qed

lemma diverges_safe :
  assumes H : "diverges gs st"
  shows "safe gs st" using H
  unfolding diverges_def safe_def imm_safe_def by blast

lemma guard_emp :
  "|gs| {P} []"
proof
  fix m :: "('a, 'b) control"
  assume H : "P (payload m)"

  assume Hc : "cont m = Inl []"

  show "safe gs m"
  proof
    fix m'

    assume Exec : "sem_exec_p gs m m'"

    hence Exec' : "rtranclp (sem_step_p gs) m m'"
      unfolding sem_exec_p_def by auto

    have Nostep : "(\<And>x1'. sem_step_p gs m x1' \<Longrightarrow> False)"
      unfolding sem_step_p_eq using Hc
      by(simp add: sem_step_def)

    have Meq : "m = m'"
      using rtranclp_nostep[OF sem_step_determ Exec' Nostep]
      by auto

    show "imm_safe gs m'"
      using Hc
      unfolding Meq imm_safe_def
      by blast
  qed
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

lemma safe_exec_safe :
  assumes H1 : "safe gs m"
  assumes H2 : "sem_exec_p gs m m'"
  shows "safe gs m'" using H2 H1 unfolding sem_exec_p_def
proof(induction rule: rtranclp_induct)
  case base
  then show ?case by blast
next
  case (step y z)

  have SafeY: "safe gs y"
    using step.prems step.IH by blast

  show ?case
  proof
    fix z'
    assume "sem_exec_p gs z z'"

    hence Exec1 : "(sem_step_p gs)\<^sup>*\<^sup>* z z'" 
      unfolding sem_exec_p_def
      by simp

    have ExecFull : "sem_exec_p gs y z'"
      using step.hyps(2) Exec1
      by auto

    show "imm_safe gs z'" using safeD[OF SafeY ExecFull] by simp
  qed
qed

      
end