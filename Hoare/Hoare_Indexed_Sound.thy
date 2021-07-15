theory Hoare_Indexed_Sound imports Hoare_Indexed Hoare
begin

(*
 * Here we show that the Hoare logic with explicit step-indexes defined in
 * Hoare_Indexed.thy is sound with respect to the one defined in Hoare.thy.
 * I do not believe the indexed Hoare logic is complete with respect to the non-indexed one,
 * but this doesn't really matter since its use is primarily in making it easier to prove
 * certain Hoare rules which are to be used in a non-indexed setting.
 *)


lemma safe_imp_safe_for :
  assumes H: "safe gs m"
  shows "safe_for gs m n" using H
proof(induction n arbitrary: m)
  case 0

  have Ex0 : "sem_exec_p gs m m"
    unfolding sem_exec_p_def by auto

  have Nostep : "sem_exec_c_p gs m 0 m" 
      by(auto intro: sem_exec_c_p.intros)

  have "imm_safe gs m" using safeD[OF 0 Ex0]
    by simp

  then consider (1) "cont m = Inl []"  |
                (2) m' where "(sem_step_p gs m m')"
    unfolding imm_safe_def by blast
  then show ?case
  proof cases
    case 1

    have "sem_exec_c_p gs m 0 m" 
      by(auto intro: sem_exec_c_p.intros)

    then show ?thesis using 1 unfolding safe_for_def by blast
  next
    case 2

    then obtain h t where Cons : "cont m = Inl (h#t)"
      unfolding sem_step_p_eq
      by(auto simp add: sem_step_def split: list.splits sum.splits)

    show ?thesis using Cons Nostep unfolding safe_for_def by blast
  qed
next
  case (Suc n)

  have Ex0 : "sem_exec_p gs m m"
    unfolding sem_exec_p_def by auto

  have "imm_safe gs m" using safeD[OF Suc.prems Ex0]
    by simp

  then consider (A) "cont m = Inl []"  |
                (B) m' where "(sem_step_p gs m m')"
    unfolding imm_safe_def by blast
  then show ?case
  proof cases
    case A

    have "sem_exec_c_p gs m 0 m" 
      by(auto intro: sem_exec_c_p.intros)

    then show ?thesis using A unfolding safe_for_def by blast
  next
    case B

    then have Exec : "sem_exec_p gs m m'"
      unfolding sem_exec_p_def by auto

    have Safe: "safe gs m'" using safe_exec_safe[OF Suc.prems Exec] by simp

    have "safe_for gs m' n" using Suc.IH[OF Safe] by simp

    then consider (B1) n0 full' where "n0 \<le> n" "sem_exec_c_p gs m' n0 full'" "cont full' = Inl []" |
                  (B2) "\<And> n0 . n0\<le>n \<Longrightarrow> \<exists>full' h t. sem_exec_c_p gs m' n0 full' \<and> cont full' = Inl (h # t)"
      unfolding safe_for_def
      by blast

    then show ?thesis 
    proof cases
      case B1

      have Conc1 : "(Suc n0) \<le> Suc n" using B1 by simp

      have Conc2 : "sem_exec_c_p gs m (Suc n0) full'" 
        using Excp_Suc[OF B B1(2)] by simp

      show ?thesis unfolding safe_for_def
        using Conc1 Conc2 B1(3)
        by blast
    next
      case B2

      have Conc' : "\<And> n0 . n0\<le>Suc n \<Longrightarrow> \<exists>full' h t. sem_exec_c_p gs m n0 full' \<and> cont full' = Inl (h # t)"
      proof-
        fix n0
        assume N0 : "n0 \<le> Suc n"
        show "\<exists>full' h t. sem_exec_c_p gs m n0 full' \<and> cont full' = Inl (h # t)"
        proof(cases n0)
          case Z' : 0

          have Conc1 : "sem_exec_c_p gs m 0 m" 
            by(auto intro: sem_exec_c_p.intros)

          obtain h t where Conc2 : "cont m = Inl (h#t)"
            using B
            unfolding sem_step_p_eq
            by(auto simp add: sem_step_def split: list.splits sum.splits)

          show ?thesis using Conc1 Conc2 unfolding Z' by blast
        next
          case Suc' : (Suc n0')

          have N0'_n : "n0' \<le> n" using N0 Suc'
            by auto

          obtain full' h t where Tail_exec : "sem_exec_c_p gs m' n0' full'" 
            and Tail_cont : "cont full' = Inl (h # t)"
            using B2[OF N0'_n] by blast

          have Full_Exec : "sem_exec_c_p gs m (Suc n0') full'"
            using Excp_Suc[OF B Tail_exec] by simp

          then show ?thesis using Tail_cont unfolding Suc' by blast
        qed
      qed

      then show ?thesis
        unfolding safe_for_def
        by blast
    qed
  qed
qed

lemma safe_for_imm_safe :
  assumes H : "safe_for gs m n"
  assumes H' : "sem_exec_c_p gs m n m'"
  shows "imm_safe gs m'"
proof-

  consider 
    (1) n0 m'_alt where "n0 \<le> n" "sem_exec_c_p gs m n0 m'_alt" "cont m'_alt = Inl []" |
    (2) "\<And> n0 . n0 \<le>n  \<Longrightarrow> \<exists>m'_alt h t. sem_exec_c_p gs m n0 m'_alt \<and> cont m'_alt = Inl (h # t)"
    using H unfolding safe_for_def
    by blast

  then show "imm_safe gs m'"
  proof cases
    case 1

    obtain m2 where Exec_start : "sem_exec_c_p gs m n0 m2"
              and Exec_finish : "sem_exec_c_p gs m2 (n - n0) m'"
      using exec_c_p_split[OF H' 1(1)]
      by blast

    have M2_m'_alt : "m2 = m'_alt"
      using exec_c_p_determ[OF 1(2) Exec_start] by simp

    (* idea: if n0 = n, we are done *)
    show ?thesis
    proof(cases "n0 = n")
      case True

      have Exec_alt_n : "sem_exec_c_p gs m n m'_alt"
        using 1 unfolding True by simp

      have M'_eq : "m'_alt = m'"
        using exec_c_p_determ[OF H' Exec_alt_n] by auto

      then show ?thesis using 1 unfolding imm_safe_def M'_eq by blast
    next
      (* otherwise we have a contradiction, since we need to execute past an Inl [] *)
      case False

      have Leq' : "1 \<le> n - n0"
        using False 1(1) by auto

      obtain mbad where Bad: "sem_exec_c_p gs m2 1 mbad"
        using exec_c_p_split[OF Exec_finish Leq'] by blast

      have Bad_step : "sem_step_p gs m2 mbad"
        using Excp_1'[OF Bad] by simp

      then obtain bad_h bad_t where Bad_nonnil : "cont m2 = Inl (bad_h#bad_t)"
        unfolding sem_step_p_eq
        by(auto simp add: sem_step_def split: sum.splits list.splits)

      hence False using 1(3) unfolding M2_m'_alt by simp

      then show ?thesis by simp
    qed
  next
    case 2

    obtain m'_alt h t where Exec_alt : "sem_exec_c_p gs m n m'_alt" and Cont_alt : "cont m'_alt = Inl (h # t)"
      using 2[of n] by blast

    have Eq : "m'_alt = m'" using exec_c_p_determ[OF H' Exec_alt] by simp

    obtain m'a where "sem_step_p gs m' m'a"
      using Cont_alt Exec_alt
      unfolding imm_safe_def Eq sem_step_p_eq sem_step_def
      by(cases h; auto)

    then show ?thesis unfolding imm_safe_def by blast
  qed
qed

lemma safe_for_imp_safe :
  assumes H : "\<And> n . safe_for gs m n"
  shows "safe gs m"
proof
  fix m'
  assume Exec : "sem_exec_p gs m m'"

  obtain n where N: "sem_exec_c_p gs m n m'"
    using exec_p_imp_exec_c_p[OF Exec] by blast

  show "imm_safe gs m'" using safe_for_imm_safe[OF H N] by simp
qed

lemma guarded_weaken :
  assumes H : "|#gs#| {#P, n1#} c"
  assumes H' : "n2 \<le> n1"
  shows "|#gs#| {#P, n2#} c"
proof
  fix m :: "('a, 'b) control"
  assume P : "P (payload m)"
  assume C : "cont m = Inl c"

  have Conc' : "safe_for gs m n1"
    using guardediD[OF H P C]
    by auto

  show "safe_for gs m n2"
    using safe_for_weaken[OF Conc' H']
    by auto
qed
    

lemma unsafe_imp_unsafe_for :
  assumes H : "\<not> safe gs m"
  shows "\<exists> n . \<not> safe_for gs m n"
  using H safe_for_imp_safe
  by blast

lemma HT'_imp_HT :
  assumes H : "HT' gs P c Q"
  shows "|gs| {-P-} c {-Q-}"
proof
  fix c'
  assume Guard : "|gs| {Q} c'"
  show "|gs| {P} (c @ c')"
  proof
    fix m :: "('a, 'b) control"
    assume Pm : "P (payload m)" 
    assume Cm : "cont m = Inl (c @ c')" 
    show "safe gs m"
    proof
      fix m'
      assume Exec : "sem_exec_p gs m m'" 

      obtain n where Execc : "sem_exec_c_p gs m n m'"
        using exec_p_imp_exec_c_p[OF Exec] by auto

      obtain npre where Npost : "|#gs#| {#-P, (npre + n)-#} c {#-Q, n-#}" using HT'D[OF H, of n]
        by blast

      have Guard'_out : "|#gs#| {#Q, n#} c'"
      proof
        fix mx :: "('a, 'b) control"
        assume Q: "Q (payload mx)"
        assume C: "cont mx = Inl c'" 

        have Safe : "safe gs mx"
          using guardedD[OF Guard Q C] by simp

        show "safe_for gs mx n"
          using safe_imp_safe_for[OF Safe] by simp
      qed

      have Guard'_in : "|#gs#| {#P, (npre + n)#} (c @ c')"
        using HTiE[OF Npost Guard'_out] by simp

      have Guard'_in' : "|#gs#| {#P, n#} (c @ c')"
        using guarded_weaken[OF Guard'_in] by simp

      have Safe' : "safe_for gs m n"
        using guardediD[OF Guard'_in' Pm Cm] by simp

      show "imm_safe gs m'"
        using safe_for_imm_safe[OF Safe' Execc] by simp
    qed
  qed
qed

(* I don't think the converse (completeness) holds in general. *)
(*
lemma HT_imp_HT' :
  assumes H : "|gs| {-P-} c {-Q-}"
  shows "HT' gs P c Q"
proof(rule HT'I)
  fix npost

(*  have Hmm : "\<And> c' . ( |gs| {Q} c' \<or> (\<exists> mbad .  *)

  have Conc' : "|#gs#| {#-P, (npost)-#} c {#-Q, npost-#}"
  proof
    fix c'
    assume G: "|#gs#| {#Q, npost#} c'"

    show "|#gs#| {#P, npost#} (c @ c')"
    proof(cases "|gs| {Q} c'")
      case True
      then show ?thesis sorry
    next
      case False

      then obtain mbad where Bad:
        "Q (payload mbad)" "cont mbad = Inl c'" "\<not> safe gs mbad"
        unfolding guarded_def
        by blast

      have Safe_post : "safe_for gs mbad npost"
        using guardediD[OF G Bad(1) Bad(2)]
        by simp

      then show ?thesis 
    qed

  show "\<exists>npre. |#gs#| {#-P, (npre + npost)-#} c {#-Q, npost-#}"
*)

(* The following is of less practical use, but still interesting: we can actually prove
 * soundness and completeness for a slightly different version of the rule - however,
 * it seems like the changes we make in doing so are precisely those that make it
 * harder to reason about loops and termination without extra assumptions on control flow... *)
(* The issue is that the existentials are nested in such a way that this doesn't work...
 * this is why we have a new construct, HT''. But, what are the implications of this...? *)
definition HT'' :: "('syn, 'mstate) semc \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> 'syn gensyn list \<Rightarrow> ('mstate \<Rightarrow> bool)\<Rightarrow> bool" where
"HT'' gs P c Q \<equiv> (\<forall> npre c' . \<exists> npost . ( |#gs#| {#Q, npost#} c' \<longrightarrow> |#gs#| {#P, npre#} (c @ c')))"

lemma HT''I :
  assumes H : "\<And> npre c' .(\<And> npost . |#gs#| {#Q, npost#} c') \<Longrightarrow> |#gs#| {#P, npre#} (c @ c')"
  shows "HT'' gs P c Q" using assms unfolding HT''_def by blast

lemma HT''D :
  assumes H : "HT'' gs P c Q"
  assumes H1 : "(\<And> npost . |#gs#| {#Q, npost#} c')"
  shows "|#gs#| {#P, npre#} (c @ c')"
  using assms unfolding HT''_def by simp

lemma HT_imp_HT'' :
  assumes H : "|gs| {-P-} c {-Q-}"
  shows "HT'' gs P c Q"
proof(rule HT''I)
  fix npre c'

  assume X : "(\<And>npost. |#gs#| {#Q, npost#} c')"

  show "|#gs#| {#P, npre#} (c @ c')"
  proof(cases "guarded gs Q c'")
    case True

    have Guard : "|gs| {P} (c @ c')" using HTE[OF H True]
      by auto

    show ?thesis
    proof
      fix m :: "('a, 'b) control"
      assume HP : "P (payload m)"
      assume CP : "cont m = Inl (c @ c')"

      show "safe_for gs m npre" using safe_imp_safe_for[OF guardedD[OF Guard HP CP]]
        by blast
    qed

  next
    case False

    then obtain bad where Bad : "Q (payload bad)" "cont bad = Inl c'" "\<not> safe gs bad"
      unfolding guarded_def
      by blast

    obtain nbad where Nbad: "\<not> safe_for gs bad nbad" using unsafe_imp_unsafe_for[OF Bad(3)]
      by blast

    then have False using guardediD[OF X[of nbad] Bad(1) Bad(2)] by blast

    thus "|#gs#| {#P, npre#} (c @ c')" by blast
  qed
qed

lemma HT''_imp_HT :
  assumes H : "HT'' gs P c Q"
  shows "|gs| {-P-} c {-Q-}"
proof
  fix c'
  assume Guard : "|gs| {Q} c'"
  show "|gs| {P} (c @ c')"
  proof
    fix m :: "('a, 'b) control"
    assume Pm : "P (payload m)" 
    assume Cm : "cont m = Inl (c @ c')" 
    show "safe gs m"
    proof
      fix m'
      assume Exec : "sem_exec_p gs m m'" 

      obtain n where Execc : "sem_exec_c_p gs m n m'"
        using exec_p_imp_exec_c_p[OF Exec] by auto

      have Guard'_out : "(\<And>npost. |#gs#| {#Q, npost#} c')"
      proof
        fix npost 
        fix mx :: "('a, 'b) control"
        assume Q: "Q (payload mx)"
        assume C: "cont mx = Inl c'" 

        have Safe : "safe gs mx"
          using guardedD[OF Guard Q C] by simp

        show "safe_for gs mx npost"
          using safe_imp_safe_for[OF Safe] by simp
      qed

      have Guard'_in : "|#gs#| {#P, n#} (c @ c')"
        using HT''D[OF H Guard'_out] by blast

      have Safe' : "safe_for gs m n"
        using guardediD[OF Guard'_in Pm Cm] by simp

      show "imm_safe gs m'"
        using safe_for_imm_safe[OF Safe' Execc] by simp
    qed
  qed
qed

end