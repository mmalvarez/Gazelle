theory Semantics_Facts imports Semantics
begin

(*
 * Various lemmas about the semantics constructs from Semantics.thy
 *)

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