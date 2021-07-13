theory Hoare_Indexed_Sound imports Hoare_Indexed Hoare
begin

(*
 * Here we show that the Hoare logic with explicit step-indexes defined in
 * Hoare_Indexed.thy is sound with respect to the one defined in Hoare.thy.
 * I do not believe the indexed Hoare logic is complete with respect to the non-indexed one,
 * but this doesn't really matter since its use is primarily in making it easier to prove
 * certain Hoare rules which are to be used in a non-indexed setting.
 *)

(* Wrapping the indexed Hoare triples to make them work like non-indexed ones.
 * The idea here is that we only care about how long the "output" (program combined with
 * the arbitrary tail quantified within the Hoare triple definition) is safe for. So, in order
 * for this to work like a normal Hoare triple, for any desired safe execution length npre,
 * we must be able to find a suffix execution
 * (safe for some npost number of steps) such that the concatenation is safe for npre. *)
definition HT' :: "('syn, 'mstate) semc \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> 'syn gensyn list \<Rightarrow> ('mstate \<Rightarrow> bool)\<Rightarrow> bool" where
"HT' gs P c Q =
  ((\<forall> npre . \<exists> npost . |#gs#| {#- P, (npre) -#} c {#- Q, npost -#}))"

lemma HT'I :
  assumes H : "(\<And> npre . \<exists> npost . |#gs#| {#- P, (npre) -#} c {#- Q, npost -#})"
  shows "HT' gs P c Q" using assms unfolding HT'_def by blast

lemma HT'D :
  assumes H : "HT' gs P c Q"
  shows "(\<And> npre . \<exists> npost . |#gs#| {#- P, (npre) -#} c {#- Q, npost -#})"
  using H unfolding HT'_def by simp

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

      obtain npost where Npost : "|#gs#| {#-P, n-#} c {#-Q, npost-#}" using HT'D[OF H, of n]
        by blast

      have Guard'_out : "|#gs#| {#Q, npost#} c'"
      proof
        fix mx :: "('a, 'b) control"
        assume Q: "Q (payload mx)"
        assume C: "cont mx = Inl c'" 

        have Safe : "safe gs mx"
          using guardedD[OF Guard Q C] by simp

        show "safe_for gs mx npost"
          using safe_imp_safe_for[OF Safe] by simp
      qed

      have Guard'_in : "|#gs#| {#P, n#} (c @ c')"
        using HTiE[OF Npost Guard'_out] by simp

      have Safe' : "safe_for gs m n"
        using guardediD[OF Guard'_in Pm Cm] by simp

      show "imm_safe gs m'"
        using safe_for_imm_safe[OF Safe' Execc] by simp
    qed
  qed
qed

(* Work in progress - concept for a limited completeness theorem, sufficient for HWhile *)

lemma HT_imp_HT' :
  assumes H : "|gs| {-P-} c {-Q-}"
  shows "HT' gs P c Q"
  unfolding HT'_def
proof
  fix npre

  show "\<exists> npost . |#gs#| {#-P, npre-#} c {#-Q, npost-#}"  using HTE[OF H]
  

  show "\<exists> npost . |#gs#| {#-P, npre-#} c {#-Q, npost-#}"  using H
  proof(induction npre arbitrary: c)
    case 0
    then show ?case  sorry (* a = 0 should work here. *)
  next
    case (Suc npre)

    obtain ahyp where Ahyp : "|#gs#| {#-P, npre-#} c {#-Q, ahyp-#}"
      using Suc.IH[OF Suc.prems]
      by blast

    show ?case using HTiE[OF Ahyp]
  qed

  have Conc' : "\<And> npost . |#gs#| {#-P, npre-#} c {#-Q, npost-#}"
  proof
    fix npost c'
    assume Gdi : "|#gs#| {#Q, npost#} c'"

(* idea: what does it mean that we fail starting at Q?
 *)

    have Meh : "|gs| {Q} c'"
    proof
      fix m :: "('a, 'b) control"
      assume Q : "Q (payload m)"
      assume Cntn : "cont m = Inl c'"
      show "safe gs m" using Gdi Q Cntn
      proof(induction 



    show "|#gs#| {#P, npre#} (c @ c')"
      using guardediD[OF Gdi] HTE[OF H]


(* idea: if no valid npost exists, then it must be the case that for this npre,
 * there is no way to get the whole program to be safe for that many steps.
 *)

  show "\<exists> npost . |#gs#| {#-P, npre-#} c {#-Q, npost-#}" 
  proof
qed


end