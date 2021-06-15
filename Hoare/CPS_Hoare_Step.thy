theory CPS_Hoare_Step imports CPS_Hoare

begin

(* Alternate version of inductive semantics used in CPS_Hoare
   with an explicit step count (useful, I hope, in certain inductive proofs)
*)

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

end