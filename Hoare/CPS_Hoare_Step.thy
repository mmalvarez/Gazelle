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

lemma Excp_1' : 
  assumes H: "sem_exec_c_p gs m1 1 m2"
  shows  "sem_step_p gs m1 m2"
  using H
proof(cases rule: sem_exec_c_p.cases)
  case Excp_0
  then show ?thesis by auto
next
  case (Excp_Suc m2' n)

  have "sem_exec_c_p gs m2' 0 m2"
    using Excp_Suc by auto

  hence "m2' = m2" 
    by(cases rule: sem_exec_c_p.cases; auto)

  then show ?thesis using Excp_Suc by auto
qed


lemma exec_c_p_split :
  assumes H : "sem_exec_c_p gs m1 n m3"
  assumes Hj : "j \<le> n"
  shows "\<exists> m2 . sem_exec_c_p gs m1 j m2 \<and> sem_exec_c_p gs m2 (n - j) m3"
  using H Hj
proof(induction arbitrary: j rule: sem_exec_c_p.induct)
  case (Excp_0 m)

  have "sem_exec_c_p gs m j m \<and> sem_exec_c_p gs m (0 - j) m"
    using sem_exec_c_p.intros(1)[of gs m] Excp_0
    by auto

  then show ?case by blast
next
  case (Excp_Suc m1 m2 n m3)
  then show ?case 
  proof(cases j)
    case 0

    have C1 : "sem_exec_c_p gs m1 0 m1"
      using sem_exec_c_p.intros(1)[of gs m1] by auto

    have C2 : "sem_exec_c_p gs m1 (Suc n) m3" using sem_exec_c_p.intros(2)[OF Excp_Suc(1) Excp_Suc(2)]
      by auto

    have "sem_exec_c_p gs m1 j m1 \<and> sem_exec_c_p gs m1 (Suc n - j) m3"
      using C1 C2 0 by auto

    then show ?thesis by blast

  next
    case (Suc j')

    hence Leq : "j' \<le> n" using Excp_Suc by auto

    obtain m2x where M2x1 : "sem_exec_c_p gs m2 j' m2x" and M2x2 : "sem_exec_c_p gs m2x (n - j') m3"
      using Excp_Suc.IH[OF Leq]
      by auto

    have "sem_exec_c_p gs m1 (j' + 1) m2x" using sem_exec_c_p.intros(2)[OF Excp_Suc(1) M2x1]
      by auto

    hence C1' : "sem_exec_c_p gs m1 (j) m2x" using Suc by auto

    have C2' : "sem_exec_c_p gs m2x (Suc n - j) m3" using M2x2 Suc Excp_Suc.prems
      by auto

    show ?thesis using C1' C2' by blast

  qed
qed

lemma exec_c_p_determ :
  assumes H1 : "sem_exec_c_p gs m1 n m2"
  assumes H2 : "sem_exec_c_p gs m1 n m2'"
  shows "m2 = m2'" using H1 H2
proof(induction arbitrary: m2' rule: sem_exec_c_p.induct)
  case (Excp_0 m)
  then show ?case 
    by(cases rule: sem_exec_c_p.cases; auto)
next
  case (Excp_Suc m1 m2 n m3)

  obtain m2_copy
    where M2_copy1 : "sem_exec_c_p gs m1 1 m2_copy" and 
      M2_copy2 :"sem_exec_c_p gs m2_copy (Suc n - 1) m2'"
    using exec_c_p_split[OF Excp_Suc.prems, of 1]
    by auto

  have Step' : "sem_step_p gs m1 m2_copy" using M2_copy1
  proof(cases rule: sem_exec_c_p.cases)
    case Excp_0
    then show ?thesis by auto
  next
    case Excp_Suc' : (Excp_Suc m2z nz)

    then have "sem_exec_c_p gs m2z 0 m2_copy"
      by auto

    hence M2_eq : "m2z = m2_copy"
      by(cases rule: sem_exec_c_p.cases; auto)

    then show ?thesis using Excp_Suc' by auto  
  qed

  have M2_eq : "m2 = m2_copy"
    using determE[OF sem_step_determ Step', of m2] Excp_Suc.hyps(1)
    by auto

  hence M2_copy2' : "sem_exec_c_p gs m2 (n) m2'"
    using M2_copy2 by auto

  show ?case using Excp_Suc.IH[OF M2_copy2'] by auto
qed

definition safe_for :: "('syn, 'mstate) semc \<Rightarrow> ('syn, 'mstate) control \<Rightarrow> nat \<Rightarrow> bool" where
"safe_for gs m n =
  (\<forall> n' m' . n' < n \<longrightarrow> sem_exec_c_p gs m n' m' \<longrightarrow> imm_safe gs m')"

lemma safe_forI [intro]:
  assumes H : "\<And> n' m' . n' < n \<Longrightarrow> sem_exec_c_p gs m n' m' \<Longrightarrow> imm_safe gs m'"
  shows "safe_for gs m n" using H unfolding safe_for_def
  by auto

lemma safe_forD :
  assumes H : "safe_for gs m n"
  assumes Hlt : "n' < n"
  assumes Hx : "sem_exec_c_p gs m n' m'"
  shows "imm_safe gs m'" using H Hx Hlt
  unfolding safe_for_def by blast

lemma safe_for_safe : "(\<And> n . safe_for gs m n) \<Longrightarrow> safe gs m"
  sorry

lemma safe_safe_for : "safe gs m \<Longrightarrow> safe_for gs m n"
  sorry



end