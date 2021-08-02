theory Hoare_Indexed
  imports
 "../Syntax/Gensyn" "../Syntax/Gensyn_Descend" "../Mergeable/Mergeable"
 "../Semantics/Semantics" "../Semantics/Semantics_Facts"
begin

(*
 * An alternate version of Hoare logic that includes explicit step-counts.
 * This ends up being useful for proving statements about control constructs that may
 * diverge (e.g. loops).
 *)

(* Captures being safe for a certain number of steps *)
definition safe_for :: "('syn, 'mstate) semc \<Rightarrow> ('syn, 'mstate) control \<Rightarrow> nat \<Rightarrow> bool" where
"safe_for gs full n =
  ((\<exists> n0 full' . n0 \<le> n \<and> sem_exec_c_p gs full n0 full' \<and> cont full' = Inl []) \<or>
   (\<forall> n0 . n0 \<le> n \<longrightarrow> (\<exists> full' h t . sem_exec_c_p gs full n0 full' \<and> cont full' = Inl (h#t))))"

lemma safe_forI_halt :
  assumes "n0 \<le> n"
  assumes "sem_exec_c_p gs full n0 full'"
  assumes "cont full' = Inl []"
  shows "safe_for gs full n"
  using assms unfolding safe_for_def by blast

lemma safe_forI_spin :
  assumes "\<And> n0 . n0 \<le> n \<Longrightarrow> (\<exists> full' h t . sem_exec_c_p gs full n0 full' \<and> cont full' = Inl (h#t))"
  shows "safe_for gs full n" using assms unfolding safe_for_def by blast

lemma exec_c_p_prefix :
  assumes H : "sem_exec_c_p gs st1 n st2"
  assumes "cont st2 = Inl z"
  assumes "n' < n"
  shows "(\<exists> st2' h' t' . sem_exec_c_p gs st1 n' st2' \<and> cont st2' = Inl (h'#t'))"
  using assms
proof(induction arbitrary: z n' rule: sem_exec_c_p.induct)
  case (Excp_0 m)

  then show ?case using Excp_0 by blast
next
  case (Excp_Suc m1 m2 n m3)
  then show ?case 
  proof(cases n')
    case 0

    have Exec0 : "sem_exec_c_p gs m1 n' m1"
      using sem_exec_c_p.intros(1)[of gs m1] unfolding 0 by auto

    obtain h t where Cont1 : "cont m1 = Inl (h#t)"
      using Excp_Suc.hyps(1)
      unfolding sem_step_p_eq sem_step_def
      by(auto split: sum.splits list.splits)

    show ?thesis using Exec0 Cont1 by blast
  next
    case (Suc n'')

    then have Lt : "n'' < n"
      using Excp_Suc.prems by auto

    obtain st2' h' t' where
      Exec2 : "sem_exec_c_p gs m2 n'' st2'" and Cont2 :"cont st2' = Inl (h'#t')"
      using Excp_Suc.IH[OF Excp_Suc.prems(1) Lt]
      by blast

    have ExecSuc : "sem_exec_c_p gs m1 (Suc n'') st2'"
      using sem_exec_c_p.intros(2)[OF Excp_Suc.hyps(1) Exec2] by auto

    show ?thesis using ExecSuc Cont2 unfolding Suc by blast
  qed
qed


lemma safe_for_weaken :
  assumes H : "safe_for gs full n"
  assumes Leq : "n' \<le> n"
  shows "safe_for gs full n'"
proof-

  consider 
    (1) n0 full' where "n0 \<le> n" "sem_exec_c_p gs full n0 full'" "cont full' = Inl []" |
    (2) "\<And> n0 . n0 \<le>n \<Longrightarrow> \<exists>full' h t. sem_exec_c_p gs full n0 full' \<and> cont full' = Inl (h # t)"
    using H unfolding safe_for_def
    by blast

  then show "safe_for gs full n'"
  proof cases
    case 1
    then show ?thesis
    proof(cases "n0 \<le> n'")
      case True

      show ?thesis using safe_forI_halt[OF True 1(2) 1(3)] by auto
    next
      case False

      hence False' : "n' < n0" by simp

      obtain mid h t where
        Exec_Mid : "sem_exec_c_p gs full n' mid" and
        Cont_Mid : "cont mid = Inl (h#t)"
        using exec_c_p_prefix[OF 1(2) 1(3) False'] by blast

      have Safe_for_prem : "(\<And>nx. nx \<le> n' \<Longrightarrow> \<exists>fullx hx tx. sem_exec_c_p gs full nx fullx \<and> cont fullx = Inl (hx # tx))"
      proof-
        fix nx

        assume Nx : "nx \<le> n'"
        hence Nx' : "nx < n0" using False' by auto

      obtain mid h t where
        Exec_Mid : "sem_exec_c_p gs full nx mid" and
        Cont_Mid : "cont mid = Inl (h#t)"
        using exec_c_p_prefix[OF 1(2) 1(3) Nx'] by blast

      then show "\<exists>fullx hx tx. sem_exec_c_p gs full nx fullx \<and> cont fullx = Inl (hx # tx)"
        by blast
    qed

    show ?thesis using safe_forI_spin[OF Safe_for_prem] by blast
  qed
  next
    case 2

    have Safe_for_prem : "(\<And>nx. nx \<le> n' \<Longrightarrow> \<exists>fullx hx tx. sem_exec_c_p gs full nx fullx \<and> cont fullx = Inl (hx # tx))"
    proof-
      fix nx
      assume Nx : "nx \<le> n'"

      have Leq' : "nx \<le> n" using Nx Leq by simp

      show "\<exists>fullx hx tx. sem_exec_c_p gs full nx fullx \<and> cont fullx = Inl (hx # tx)"
        using 2[OF Leq'] by blast
    qed

    then show ?thesis using safe_forI_spin[OF Safe_for_prem] by blast
  qed
qed

lemma safe_for_extend :
  assumes H : "safe_for gs st2 n2"
  assumes Hexec : "sem_exec_c_p gs st1 n1 st2"
  shows "safe_for gs st1 (n1 + n2)" using Hexec H
proof(induction arbitrary: n2 rule: sem_exec_c_p.induct)
  case (Excp_0 m)
  then show ?case by simp
next
  case (Excp_Suc m1 m2 n m3)

  have Safe2 : "safe_for gs m2 (n + n2)"
    using Excp_Suc.IH[OF Excp_Suc.prems(1)] by simp

  consider 
    (1) n0 full' where "n0 \<le> n + n2" "sem_exec_c_p gs m2 n0 full'" "cont full' = Inl []" |
    (2) "\<And> n0 . n0 \<le>n + n2 \<Longrightarrow> \<exists>full' h t. sem_exec_c_p gs m2 n0 full' \<and> cont full' = Inl (h # t)"
    using Safe2 unfolding safe_for_def
    by blast

  then show ?case
  proof cases
    case 1

    have Exec : "sem_exec_c_p gs m1 (Suc n0) full'"
      using sem_exec_c_p.intros(2)[OF Excp_Suc.hyps(1) 1(2)] by simp

    have Leq : "Suc n0 \<le> Suc n + n2 " using 1(1) by simp

    show ?thesis using safe_forI_halt[OF Leq Exec 1(3)] by simp
  next
    case 2

    have Safe_for_prem :
      "(\<And>n0. n0 \<le> (Suc n + n2) \<Longrightarrow> \<exists>full' h t. sem_exec_c_p gs m1 n0 full' \<and> cont full' = Inl (h # t))"
    proof-
      fix n0
      assume N0 : "n0 \<le> Suc n + n2"

      show "\<exists>full' h t. sem_exec_c_p gs m1 n0 full' \<and> cont full' = Inl (h # t)"
      proof(cases n0)
        case 0

        have Exec0 : "sem_exec_c_p gs m1 n0 m1"
          using sem_exec_c_p.intros(1)[of gs m1] unfolding 0 by simp

        obtain h t where Cont0 : "cont m1 = Inl (h # t)"
          using Excp_Suc.hyps(1) unfolding sem_step_p_eq sem_step_def
          by(auto split: sum.splits list.splits)

        show ?thesis using Exec0 Cont0 by blast
      next
        case (Suc n0')

        have Leq' : "n0' \<le> n + n2" using Suc N0 by simp

        obtain m2' h t where M2_exec : "sem_exec_c_p gs m2 n0' m2'" and M2_cont : "cont m2' = Inl (h # t)"
          using 2[OF Leq'] by blast

        have Exec_Suc : "sem_exec_c_p gs m1 n0 m2'"
          using sem_exec_c_p.intros(2)[OF Excp_Suc.hyps(1) M2_exec] 
          unfolding Suc by simp

        show ?thesis using Exec_Suc M2_cont by blast
      qed
    qed

    show ?thesis using safe_forI_spin[OF Safe_for_prem, of "Suc n + n2"] by simp
  qed
qed

(* Indexed version of guarded (capturing the idea that starting in a state satisfying P
 * means we are safe for a certain number of steps)
 *)
definition guarded :: "('syn, 'mstate) semc \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'syn gensyn list \<Rightarrow> bool"
("|#_#| {#_, _#} _" [210, 212, 214, 216])
 where
"guarded gs P n c =
  (\<forall> m . P (payload m) \<longrightarrow> cont m = Inl c \<longrightarrow> safe_for gs m n)"

lemma guardediI [intro] :
  assumes H : "\<And> m . P (payload m) \<Longrightarrow> cont m = Inl c \<Longrightarrow> safe_for gs m n"
  shows "guarded gs P n c" using H
  unfolding guarded_def
  by auto

lemma guardediD :
  assumes H : "guarded gs P n c"
  assumes HP : "P (payload m)"
  assumes Hcont : "cont m = Inl c"
  shows "safe_for gs m n" using assms
  unfolding guarded_def by blast

(* Our indexed Hoare triple. The basic idea here is that we limit the number of steps we are
 * required to be safe for, both on the "input" (|gs| {Q, nq} (c')) 
 * and the "output" (|gs| {P, np} (c @ c')) *)
definition HT :: "('syn, 'mstate) semc \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'syn gensyn list \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" 
  ("|#_#| {#-_, _-#} _ {#-_, _-#}" [220, 222, 224, 226, 228, 230])
  where
"HT gs P np c Q nq =
  (\<forall> c' . |#gs#| {#Q, nq#} (c') \<longrightarrow> |#gs#| {#P, np#} (c @ c'))"

lemma HTiI [intro] :
  assumes H : "\<And> c' . |#gs#| {#Q, nq#} (c') \<Longrightarrow> |#gs#| {#P, np#} (c @ c')"
  shows "HT gs P np c Q nq" using H unfolding HT_def
  by auto

lemma HTiE [elim]:
  assumes H : "HT gs P np c Q nq"
  assumes H' : "|#gs#| {#Q, nq#} c'"
  shows "|#gs#| {#P, np#} (c@c')" using assms
  unfolding HT_def
  by auto

lemma HConseq :
  assumes H : "|#gs#| {#- P', np' -#} c {#-Q', nq'-#}"
  assumes HP1 : "\<And> st . P st \<Longrightarrow> P' st"
  assumes HP2 : "np \<le> np'"
  assumes HQ1 : "\<And> st . Q' st \<Longrightarrow> Q st"
  assumes HQ2 : "nq' \<le> nq"
  shows "|#gs#| {#-P, np-#} c {#-Q, nq-#}"
proof(rule HTiI)
  fix c'
  assume Exec : "|#gs#| {#Q, nq#} c'"

  have Exec' : "|#gs#| {#Q', nq'#} c'"
  proof
    fix m :: "('a, 'b) control"
    assume Q' : "Q' (payload m)"
    assume C : "cont m = Inl c'"

    have Q : "Q (payload m)" using HQ1[OF Q'] by simp

    have Conc' : "safe_for gs m nq"
      using guardediD[OF Exec Q C] by auto

    show "safe_for gs m nq'"
      using safe_for_weaken[OF Conc' HQ2] by auto
  qed

  then have Exec'' :"|#gs#| {#P', np'#} (c@c')"
    using HTiE[OF H Exec'] by auto

  show "|#gs#| {#P, np#} (c @ c')"
  proof
    fix m :: "('a, 'b) control"
    assume P: "P (payload m)"
    assume C : "cont m = Inl (c @ c')"

    have P' : "P' (payload m)" using HP1[OF P] by simp

    have Conc' : "safe_for gs m np'"
      using guardediD[OF Exec'' P' C] by auto

    show "safe_for gs m np"
      using safe_for_weaken[OF Conc' HP2] by auto
  qed
qed

lemma HCat :
  assumes H : "|#gs#| {#- P1, np1 -#} c1 {#- P2, np2 -#}"
  assumes H' : "|#gs#| {#- P2, np2 -#} c2 {#- P3, np3 -#}"
  shows "|#gs#| {#- P1, np1 -#} (c1 @ c2) {#- P3, np3 -#}"
proof(rule HTiI)
  fix c'
  assume HP3 : "|#gs#| {#P3, np3#} c'"

  have P2_cont : "|#gs#| {#P2, np2#} (c2 @ c')"
    using HTiE[OF H' HP3]
    by auto

  show "|#gs#| {#P1, np1#} ((c1 @ c2) @ c')"
    using HTiE[OF H P2_cont]
    unfolding append_assoc
    by auto
qed

(* Wrapping the indexed Hoare triples to make them work like non-indexed ones.
 * The idea here is that we only care about how long the "output" (program combined with
 * the arbitrary tail quantified within the Hoare triple definition) is safe for. So, in order
 * for this to work like a normal Hoare triple, for any desired safe execution length npre,
 * we must be able to find a suffix execution
 * (safe for some npost number of steps) such that the concatenation is safe for npre. *)
definition HT' :: "('syn, 'mstate) semc \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> 'syn gensyn list \<Rightarrow> ('mstate \<Rightarrow> bool)\<Rightarrow> bool" 
  ("|_| {~_~} _ {~_~}" [250, 252, 254, 256])  
  where
"HT' gs P c Q =
  ((\<forall> npost . \<exists> npre . |#gs#| {#- P, (npre + npost) -#} c {#- Q, npost -#}))"

lemma HT'I :
  assumes H : "(\<And> npost. \<exists> npre . |#gs#| {#- P, (npre + npost) -#} c {#- Q, npost -#})"
  shows "HT' gs P c Q" using assms unfolding HT'_def by blast

lemma HT'D :
  assumes H : "HT' gs P c Q"
  shows "(\<And> npost . \<exists> npre . |#gs#| {#- P, (npre + npost) -#} c {#- Q, npost -#})"
  using H unfolding HT'_def by simp

(* Consequence and Cat for our wrapped Hoare triple. 
 * Rules using the "wrapped" indexed Hoare logic HT' will have names starting with Hx.
 *)

lemma HT'Conseq :
  assumes H : "|gs| {~ P'~} c {~Q'~}"
  assumes HP1 : "\<And> st . P st \<Longrightarrow> P' st"
  assumes HQ1 : "\<And> st . Q' st \<Longrightarrow> Q st"
  shows "|gs| {~P~} c {~Q~}"
proof(rule HT'I)
  fix npre

  obtain npre'
    where Npre' : "|#gs#| {#-P', (npre' + npre) -#} c {#-Q', npre-#}"
    using HT'D[OF H, of npre]
    by blast

  have "|#gs#| {#-P, (0 + npre) -#} c {#-Q, npre-#}"
    using HConseq[OF Npre', of P npre Q npre] HP1 HQ1
    by(auto)

  then show "\<exists>npre''. |#gs#| {#-P, (npre'' + npre)-#} c {#-Q, npre-#}"
    by blast
qed

lemma HT'Cat :
  assumes H : "|gs| {~ P1 ~} c1 {~ P2 ~}"
  assumes H' : "|gs| {~ P2 ~} c2 {~ P3 ~}"
  shows "|gs| {~ P1 ~} (c1 @ c2) {~ P3 ~}"
proof(rule HT'I)
  fix npre

  obtain n1
    where N1 : "|#gs#| {#-P1, (n1 + npre)-#} c1 {#-P2, npre-#}"
    using HT'D[OF H]
    by blast

  obtain n2
    where N2 : "|#gs#| {#-P2, (n2 + npre)-#} c2 {#-P3, npre-#}"
    using HT'D[OF H']
    by blast

  have N2' : "|#gs#| {#-P2, (npre)-#} c2 {#-P3, npre-#}"
    using HConseq[OF N2, of P2 npre P3 npre] by auto


  show "\<exists>n3. |#gs#| {#-P1, (n3 + npre)-#} (c1 @ c2) {#-P3, npre-#}"
    using HCat[OF N1 N2'] by blast
qed

lemma HT'Cons :
  assumes H : "|gs| {~P1~} [c] {~P2~}"
  assumes H' : "|gs| {~P2~} cs {~P3~}"
  shows "|gs| {~P1~} (c#cs) {~P3~}"
  using HT'Cat[OF H H']
  by auto

lemma HT'D0 :
  assumes H : "HT' gs P c Q"
  shows "(\<And> npost . |#gs#| {#- P, (npost) -#} c {#- Q, npost -#})"
proof-
  fix npost

  obtain npre where Npre : "|#gs#| {#- P, (npre + npost) -#} c {#- Q, npost -#}"
    using HT'D[OF H] by blast

  show "|#gs#| {#-P, npost-#} c {#-Q, npost-#}"
    using HConseq[OF Npre, of P npost Q npost] by auto
qed

end