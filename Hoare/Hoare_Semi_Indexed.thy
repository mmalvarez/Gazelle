theory Hoare_Semi_Indexed
  imports
 "../Syntax/Gensyn" "../Syntax/Gensyn_Descend" "../Mergeable/Mergeable"
 "../Semantics/Semantics" "../Semantics/Semantics_Facts" "Hoare"
begin

(*
 * An alternate version of Hoare logic that includes one exp step-count.
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
definition HT :: "('syn, 'mstate) semc \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'syn gensyn list \<Rightarrow> ('mstate \<Rightarrow> bool)  \<Rightarrow> bool" 
  ("|#_#| {#-_, _-#} _ {#-_-#}" [220, 222, 224, 226, 230])
  where
"HT gs P np c Q =
  (\<forall> c' . |#gs#| {#Q, np#} (c') \<longrightarrow> |#gs#| {#P, np#} (c @ c'))"

lemma HTiI [intro] :
  assumes H : "\<And> c' . |#gs#| {#Q, np#} (c') \<Longrightarrow> |#gs#| {#P, np#} (c @ c')"
  shows "HT gs P np c Q " using H unfolding HT_def
  by auto

lemma HTiE [elim]:
  assumes H : "HT gs P np c Q"
  assumes H' : "|#gs#| {#Q, np#} (c')"
  shows "|#gs#| {#P, np#} (c@c')" using assms
  unfolding HT_def
  by auto

lemma HConseq :
  assumes H : "|#gs#| {#- P', np -#} c {#-Q'-#}"
  assumes HP1 : "\<And> st . P st \<Longrightarrow> P' st"
  assumes HQ1 : "\<And> st . Q' st \<Longrightarrow> Q st"
  shows "|#gs#| {#-P, np-#} c {#-Q-#}"
proof(rule HTiI)
  fix c'
  assume Exec : "|#gs#| {#Q, np#} c' "

  have Exec' : "|#gs#| {#Q', np#} c'"
  proof
    fix m :: "('a, 'b) control"
    assume Q' : "Q' (payload m)"
    assume C : "cont m = Inl c'"

    have Q : "Q (payload m)" using HQ1[OF Q'] by simp

    have Conc' : "safe_for gs m np"
      using guardediD[OF Exec Q C] by auto

    then show "safe_for gs m np"
      by auto
  qed

  then have Exec'' :"|#gs#| {#P', np#} (c@c')"
    using HTiE[OF H Exec'] by auto

  show "|#gs#| {#P, np#} (c @ c')"
  proof
    fix m :: "('a, 'b) control"
    assume P: "P (payload m)"
    assume C : "cont m = Inl (c @ c')"

    have P' : "P' (payload m)" using HP1[OF P] by simp

    have Conc' : "safe_for gs m np"
      using guardediD[OF Exec'' P' C] by auto

    then show "safe_for gs m np" by auto
  qed
qed

lemma HCat :
  assumes H : "|#gs#| {#- P1, np -#} c1 {#- P2 -#}"
  assumes H' : "|#gs#| {#- P2, np -#} c2 {#- P3 -#}"
  shows "|#gs#| {#- P1, np -#} (c1 @ c2) {#- P3 -#}"
proof(rule HTiI)
  fix c'
  assume HP3 : "|#gs#| {#P3, np#} c'"

  have P2_cont : "|#gs#| {#P2, np#} (c2 @ c')"
    using HTiE[OF H' HP3]
    by auto

  show "|#gs#| {#P1, np#} ((c1 @ c2) @ c')"
    using HTiE[OF H P2_cont] unfolding append_assoc by blast
qed


(* Comparing our Hoare definitions to classic Appel-style ones. *)
(* Here are the classic definitions ("c" for classic) *)
(*
definition imm_safe :: "('syn, 'mstate) semc \<Rightarrow> ('syn, 'mstate) control  \<Rightarrow> bool" where
"imm_safe gs m \<equiv>
 ((s_cont m = Inl []) \<or>
  (\<exists> m' . sem_step_p gs m m'))"


definition safec :: "('syn, 'mstate) semc \<Rightarrow> ('syn, 'mstate) control \<Rightarrow> bool" where
"safec gs m \<equiv>
  (\<forall> m' . sem_exec_p gs m m' \<longrightarrow> imm_safe gs m')"

lemma safecI [intro]:
  assumes H : "\<And> m' . sem_exec_p gs m m' \<Longrightarrow> imm_safe gs m'"
  shows "safec gs m" using H unfolding safec_def
  by auto

lemma safecD :
  assumes H : "safec gs m"
  assumes Hx : "sem_exec_p gs m m'"
  shows "imm_safe gs m'" using H Hx
  unfolding safec_def by blast

definition guardedc :: "('syn, 'mstate) semc \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> 'syn gensyn list \<Rightarrow> bool"
 where
"guardedc gs P c =
  (\<forall> m . P (payload m) \<longrightarrow> s_cont m = Inl c \<longrightarrow> safec gs m)"

lemma guardedcI [intro] :
  assumes H : "\<And> m . P (payload m) \<Longrightarrow> s_cont m = Inl c \<Longrightarrow> safec gs m"
  shows "guardedc gs P c" using H
  unfolding guardedc_def
  by auto

lemma guardedcD :
  assumes H : "guardedc gs P c"
  assumes HP : "P (payload m)"
  assumes Hcont : "s_cont m = Inl c"
  shows "safec gs m" using assms
  unfolding guardedc_def by blast

definition HTc :: "('syn, 'mstate) semc \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> 'syn gensyn list \<Rightarrow> ('mstate \<Rightarrow> bool)\<Rightarrow> bool" 
  where
"HTc gs P c Q =
  (\<forall> c' .  guardedc gs Q c' \<longrightarrow> guardedc gs P (c @ c'))"

lemma HTcI [intro] :
  assumes H : "\<And> c' . guardedc gs Q c' \<Longrightarrow> guardedc gs P (c @ c')"
  shows "HTc gs P c Q" using H unfolding HTc_def
  by auto

lemma HTcE [elim]:
  assumes H : "HTc gs P c Q"
  assumes H' : "guardedc gs Q c'"
  shows "guardedc gs P (c @ c')" using assms
  unfolding HTc_def
  by auto
*)
(* Now, we implement "classic" HT using our primitives, and show that it behaves the same *)
(* NB: we may need to add the dual of this to our definition. *)

(* TODO - unless unnecessary *)
(*
lemma safe_for_imp_safec :
  assumes H: "\<And> n . safe_for gs m n"
  shows "safec gs m"
  sorry

(* TODO - unless unnecessary*)
lemma safec_imp_safe_for :
  assumes H: "safec gs m"
  shows "safe_for gs m n"
  sorry

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

    (* idea: n0 = n, because otherwise we would execute past a Inl [] (contradiction) *)

    show ?thesis sorry
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
lemma HTc'_imp_HTc :
  assumes H : "HTc' gs P c Q"
  shows "HTc gs P c Q"
proof
  fix c'
  assume Guard : "guardedc gs Q c'"
  show "guardedc gs P (c @ c')"
  proof
    fix m :: "('a, 'b) control"
    assume Pm : "P (payload m)" 
    assume Cm : "s_cont m = Inl (c @ c')" 
    show "safec gs m"
    proof
      fix m'
      assume Exec : "sem_exec_p gs m m'" 

      obtain n where Execc : "sem_exec_c_p gs m n m'"
        using exec_p_imp_exec_c_p[OF Exec] by auto

      obtain npost where Npost : "|gs| {-P, n-} c {-Q, npost-}" using HTc'D[OF H, of n]
        by blast

      have Guard'_out : "|gs| {Q, npost} c'"
      proof
        fix mx :: "('a, 'b) control"
        assume Q: "Q (payload mx)"
        assume C: "s_cont mx = Inl c'" 

        have Safe : "safec gs mx"
          using guardedcD[OF Guard Q C] by simp

        show "safe_for gs mx npost"
          using safec_imp_safe_for[OF Safe] by simp
      qed

      have Guard'_in : "|gs| {P, n} c @ c'"
        using HTE[OF Npost Guard'_out] by simp

      have Safe' : "safe_for gs m n"
        using guardedD[OF Guard'_in Pm Cm] by simp

      show "imm_safe gs m'"
        using safe_for_imm_safe[OF Safe' Execc] by simp
    qed
  qed
qed
*)

end