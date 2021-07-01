theory CPS_Hoare_Steps
  imports
 "../Gensyn" "../Gensyn_Descend" "../Mergeable/Mergeable"
 "../Lifting/LiftUtils" "../Lifting/LiftInstances" "../Lifting/LangCompFull"
 "../Relpath" "../Semantics/Gensyn_Sem_Small" "Hoare_Core" "CPS_Hoare_Step"
begin

definition safe_for :: "('syn, 'mstate) semc \<Rightarrow> ('syn, 'mstate) control \<Rightarrow> nat \<Rightarrow> bool" where
"safe_for gs full n =
  ((\<exists> n0 full' . n0 \<le> n \<and> sem_exec_c_p gs full n0 full' \<and> s_cont full' = Inl []) \<or>
   (\<forall> n0 . n0 \<le> n \<longrightarrow> (\<exists> full' h t . sem_exec_c_p gs full n0 full' \<and> s_cont full' = Inl (h#t))))"

lemma safe_forI_halt :
  assumes "n0 \<le> n"
  assumes "sem_exec_c_p gs full n0 full'"
  assumes "s_cont full' = Inl []"
  shows "safe_for gs full n"
  using assms unfolding safe_for_def by blast

lemma safe_forI_spin :
  assumes "\<And> n0 . n0 \<le> n \<Longrightarrow> (\<exists> full' h t . sem_exec_c_p gs full n0 full' \<and> s_cont full' = Inl (h#t))"
  shows "safe_for gs full n" using assms unfolding safe_for_def by blast

lemma exec_c_p_prefix :
  assumes H : "sem_exec_c_p gs st1 n st2"
  assumes "s_cont st2 = Inl z"
  assumes "n' < n"
  shows "(\<exists> st2' h' t' . sem_exec_c_p gs st1 n' st2' \<and> s_cont st2' = Inl (h'#t'))"
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

    obtain h t where Cont1 : "s_cont m1 = Inl (h#t)"
      using Excp_Suc.hyps(1)
      unfolding sem_step_p_eq sem_step_def
      by(auto split: sum.splits list.splits)

    show ?thesis using Exec0 Cont1 by blast
  next
    case (Suc n'')

    then have Lt : "n'' < n"
      using Excp_Suc.prems by auto

    obtain st2' h' t' where
      Exec2 : "sem_exec_c_p gs m2 n'' st2'" and Cont2 :"s_cont st2' = Inl (h'#t')"
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
    (1) n0 full' where "n0 \<le> n" "sem_exec_c_p gs full n0 full'" "s_cont full' = Inl []" |
    (2) "\<And> n0 . n0 \<le>n \<Longrightarrow> \<exists>full' h t. sem_exec_c_p gs full n0 full' \<and> s_cont full' = Inl (h # t)"
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
        Cont_Mid : "s_cont mid = Inl (h#t)"
        using exec_c_p_prefix[OF 1(2) 1(3) False'] by blast

      have Safe_for_prem : "(\<And>nx. nx \<le> n' \<Longrightarrow> \<exists>fullx hx tx. sem_exec_c_p gs full nx fullx \<and> s_cont fullx = Inl (hx # tx))"
      proof-
        fix nx

        assume Nx : "nx \<le> n'"
        hence Nx' : "nx < n0" using False' by auto

      obtain mid h t where
        Exec_Mid : "sem_exec_c_p gs full nx mid" and
        Cont_Mid : "s_cont mid = Inl (h#t)"
        using exec_c_p_prefix[OF 1(2) 1(3) Nx'] by blast

      then show "\<exists>fullx hx tx. sem_exec_c_p gs full nx fullx \<and> s_cont fullx = Inl (hx # tx)"
        by blast
    qed

    show ?thesis using safe_forI_spin[OF Safe_for_prem] by blast
  qed
  next
    case 2

    have Safe_for_prem : "(\<And>nx. nx \<le> n' \<Longrightarrow> \<exists>fullx hx tx. sem_exec_c_p gs full nx fullx \<and> s_cont fullx = Inl (hx # tx))"
    proof-
      fix nx
      assume Nx : "nx \<le> n'"

      have Leq' : "nx \<le> n" using Nx Leq by simp

      show "\<exists>fullx hx tx. sem_exec_c_p gs full nx fullx \<and> s_cont fullx = Inl (hx # tx)"
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
    (1) n0 full' where "n0 \<le> n + n2" "sem_exec_c_p gs m2 n0 full'" "s_cont full' = Inl []" |
    (2) "\<And> n0 . n0 \<le>n + n2 \<Longrightarrow> \<exists>full' h t. sem_exec_c_p gs m2 n0 full' \<and> s_cont full' = Inl (h # t)"
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
      "(\<And>n0. n0 \<le> (Suc n + n2) \<Longrightarrow> \<exists>full' h t. sem_exec_c_p gs m1 n0 full' \<and> s_cont full' = Inl (h # t))"
    proof-
      fix n0
      assume N0 : "n0 \<le> Suc n + n2"

      show "\<exists>full' h t. sem_exec_c_p gs m1 n0 full' \<and> s_cont full' = Inl (h # t)"
      proof(cases n0)
        case 0

        have Exec0 : "sem_exec_c_p gs m1 n0 m1"
          using sem_exec_c_p.intros(1)[of gs m1] unfolding 0 by simp

        obtain h t where Cont0 : "s_cont m1 = Inl (h # t)"
          using Excp_Suc.hyps(1) unfolding sem_step_p_eq sem_step_def
          by(auto split: sum.splits list.splits)

        show ?thesis using Exec0 Cont0 by blast
      next
        case (Suc n0')

        have Leq' : "n0' \<le> n + n2" using Suc N0 by simp

(*
        have Exec_Suc : "sem_exec_c_p gs m1 n0 m3"
          using sem_exec_c_p.intros(2)[OF Excp_Suc.hyps(1) Excp_Suc.hyps(2)] 
          unfolding Suc by simp
*)

        obtain m2' h t where M2_exec : "sem_exec_c_p gs m2 n0' m2'" and M2_cont : "s_cont m2' = Inl (h # t)"
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

(* We need to compare all of these to Appel's versions to make the case that we are saying the same thing. *) 


definition guarded :: "('syn, 'mstate) semc \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'syn gensyn list \<Rightarrow> bool"
("|_| {_, _} _")
 where
"guarded gs P n c =
  (\<forall> m . P (payload m) \<longrightarrow> s_cont m = Inl c \<longrightarrow> safe_for gs m n)"

lemma guardedI [intro] :
  assumes H : "\<And> m . P (payload m) \<Longrightarrow> s_cont m = Inl c \<Longrightarrow> safe_for gs m n"
  shows "guarded gs P n c" using H
  unfolding guarded_def
  by auto

lemma guardedD :
  assumes H : "guarded gs P n c"
  assumes HP : "P (payload m)"
  assumes Hcont : "s_cont m = Inl c"
  shows "safe_for gs m n" using assms
  unfolding guarded_def by blast

(* question: what is the right way to capture the relationship between "safe_for"? do we want to be capturing more dependencies? *)
(* what should np be?
probably want it to take c' and nq
do we also want it to take c?
*)
definition HT :: "('syn, 'mstate) semc \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'syn gensyn list \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" 
  ("|_| {-_, _-} _ {-_, _-}")
  where
"HT gs P np c Q nq =
  (\<forall> c' . |gs| {Q, nq} (c') \<longrightarrow> |gs| {P, np} (c @ c'))"

lemma HTI [intro] :
  assumes H : "\<And> c' . |gs| {Q, nq} (c') \<Longrightarrow> |gs| {P, np} (c @ c')"
  shows "HT gs P np c Q nq" using H unfolding HT_def
  by auto

lemma HTE [elim]:
  assumes H : "HT gs P np c Q nq"
  assumes H' : "|gs| {Q, nq} c'"
  shows "|gs| {P, np} (c@c')" using assms
  unfolding HT_def
  by auto

lemma HConseq :
  assumes H : "|gs| {- P', np' -} c {-Q', nq'-}"
  assumes HP1 : "\<And> st . P st \<Longrightarrow> P' st"
  assumes HP2 : "np \<le> np'"
  assumes HQ1 : "\<And> st . Q' st \<Longrightarrow> Q st"
  assumes HQ2 : "nq' \<le> nq"
  shows "|gs| {-P, np-} c {-Q, nq-}"
proof(rule HTI)
  fix c'
  assume Exec : "|gs| {Q, nq} c'"

  have Exec' : "|gs| {Q', nq'} c'"
  proof
    fix m :: "('a, 'b) control"
    assume Q' : "Q' (payload m)"
    assume C : "s_cont m = Inl c'"

    have Q : "Q (payload m)" using HQ1[OF Q'] by simp

    have Conc' : "safe_for gs m nq"
      using guardedD[OF Exec Q C] by auto

    show "safe_for gs m nq'"
      using safe_for_weaken[OF Conc' HQ2] by auto
  qed

  then have Exec'' :"|gs| {P', np'} c@c'"
    using HTE[OF H Exec'] by auto

  show "|gs| {P, np} c @ c'"
  proof
    fix m :: "('a, 'b) control"
    assume P: "P (payload m)"
    assume C : "s_cont m = Inl (c @ c')"

    have P' : "P' (payload m)" using HP1[OF P] by simp

    have Conc' : "safe_for gs m np'"
      using guardedD[OF Exec'' P' C] by auto

    show "safe_for gs m np"
      using safe_for_weaken[OF Conc' HP2] by auto
  qed
qed

lemma HCat :
  assumes H : "|gs| {- P1, np1 -} c1 {- P2, np2 -}"
  assumes H' : "|gs| {- P2, np2 -} c2 {- P3, np3 -}"
  shows "|gs| {- P1, np1 -} c1 @ c2 {- P3, np3 -}"
proof(rule HTI)
  fix c'
  assume HP3 : "|gs| {P3, np3} c'"

  have P2_cont : "|gs| {P2, np2} c2 @ c'"
    using HTE[OF H' HP3]
    by auto

  show "|gs| {P1, np1} (c1 @ c2) @ c'"
    using HTE[OF H P2_cont]
    unfolding append_assoc
    by auto
qed


(* Comparing our Hoare definitions to classic Appel-style ones. *)
(* Here are the classic definitions ("c" for classic) *)

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

(* Now, we implement "classic" HT using our primitives, and show that it behaves the same *)
(* NB: we may need to add the dual of this to our definition. *)

(* TODO - unless unnecessary *)
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
    (1) n0 m'_alt where "n0 \<le> n" "sem_exec_c_p gs m n0 m'_alt" "s_cont m'_alt = Inl []" |
    (2) "\<And> n0 . n0 \<le>n  \<Longrightarrow> \<exists>m'_alt h t. sem_exec_c_p gs m n0 m'_alt \<and> s_cont m'_alt = Inl (h # t)"
    using H unfolding safe_for_def
    by blast

  then show "imm_safe gs m'"
  proof cases
    case 1

    (* idea: n0 = n, because otherwise we would execute past a Inl [] (contradiction) *)

    show ?thesis sorry
  next
    case 2

    obtain m'_alt h t where Exec_alt : "sem_exec_c_p gs m n m'_alt" and Cont_alt : "s_cont m'_alt = Inl (h # t)"
      using 2[of n] by blast

    have Eq : "m'_alt = m'" using exec_c_p_determ[OF H' Exec_alt] by simp

    obtain m'a where "sem_step_p gs m' m'a"
      using Cont_alt Exec_alt
      unfolding imm_safe_def Eq sem_step_p_eq sem_step_def
      by(cases h; auto)

    then show ?thesis unfolding imm_safe_def by blast
  qed
qed

(*"(\<And> npost . \<exists> npre . |gs| {- P, (npre) -} c {- Q, npost -})"*)
definition HTc' :: "('syn, 'mstate) semc \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> 'syn gensyn list \<Rightarrow> ('mstate \<Rightarrow> bool)\<Rightarrow> bool" where
"HTc' gs P c Q =
  ((\<forall> npre . \<exists> npost . |gs| {- P, (npre) -} c {- Q, npost -}))"

lemma HTc'I :
  assumes H : "(\<And> npre . \<exists> npost . |gs| {- P, (npre) -} c {- Q, npost -})"
  shows "HTc' gs P c Q" using assms unfolding HTc'_def by blast

lemma HTc'D :
  assumes H : "HTc' gs P c Q"
  shows "(\<And> npre . \<exists> npost . |gs| {- P, (npre) -} c {- Q, npost -})"
  using H unfolding HTc'_def by simp

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

(* this direction is going to be frustrating, and is less important.
i am ok leaving this as a TODO.
*)

(*
lemma HTc_imp_HTc'_alt :
  assumes H : "HTc gs P c Q"
  shows "\<forall>npre. \<exists> npost . (HT gs P npre c Q npost) \<and> npre \<le> npost"
proof
  fix npre

  show "\<exists> npost . |gs| {-P, npre-} c {-Q, npost-} \<and> npre \<le> npost"
    unfolding HT_def
    apply(auto)

  show "\<exists> npost . (HT gs P npre c Q npost) \<and> npre \<le> npost" using H
  proof(induction npre arbitrary: c)
    case 0
    then show ?case sorry
  next
    case (Suc npre)
    then show ?case sorry
  qed
*)
lemma HTc_imp_HTc' :
  assumes H : "HTc gs P c Q"
  shows "HTc' gs P c Q" unfolding HTc'_def
proof(step; step)
  fix npre

  show "|gs| {-P, npre-} c {-Q, npre-}"
  proof(induction npre)
    case 0
    then show ?case sorry
  next
    case (Suc npre)
    show ?case
    proof
      fix c'
      assume "|gs| {Q, Suc npre} c'"
      show "|gs| {P, Suc npre} c @ c'"
      
      
      using HTcE[OF H]
  qed


  show "Ex (HT gs P npre c Q)"
    unfolding HT_def
    using HTcE[OF H]
(*  sorry *)
(*
proof-
  have "\<And> npost npre . |gs| {-P, npre-} c {-Q, npost-}"
  proof

    fix npre c'

    fix c'

    have "(\<And> npost. |gs| {Q, npost} c') \<Longrightarrow> |gs| {P, npre} c @ c'"
      using HTcE[OF H]

    fix npre npost c'
    assume X : "|gs| {Q, npost} c'"

    have Conc' : "guardedc gs Q c'"
    proof
      fix m :: "('a, 'b) control"
      assume Qm : "Q (payload m)"
      assume Cm : "s_cont m = Inl c'"
      show "safec gs m" using X Qm Cm


    show "|gs| {P, npre} c @ c'" using HTcE[OF H]
*)
(*
proof-
  have "\<And> npre npost . |gs| {-P, npre-} c {-Q, npost-}"
  proof
    fix npre npost c'
    assume X : "|gs| {Q, npost} c'"

    show "|gs| {P, npre} c @ c'"
    proof
      fix m :: "('a, 'b) control"
      assume Pm : "P (payload m)"
      assume Cm : "s_cont m = Inl (c @ c')"

      show "safe_for gs m npre"
    proof(induction npre arbitrary: c)
      case 0
      show "safe_for gs m 0" sorry (* by cases on c@c' *)
    next
      case (Suc npre)

      obtain npost' where NP' : "|gs| {-P, npre-} c {-Q, npost'-}"
        using Suc 

      show ?case unfolding HT_def
      proof(cases "guardedc gs Q c")
        case False

        then obtain mbad where Mbad : "Q (payload mbad)" "s_cont mbad = Inl c" "\<not> safec gs mbad"
          unfolding guardedc_def
          by blast

        then obtain mbad' where Mbad' : "sem_exec_p gs mbad mbad'" "\<not> imm_safe gs mbad'"
          unfolding safec_def by blast

        obtain nbad where Nbad : "sem_exec_c_p gs mbad nbad mbad'"
          using exec_p_imp_exec_c_p[OF Mbad'(1)] by blast

        show "\<exists>a. \<forall>c'. |gs| {Q, a} c' \<longrightarrow> |gs| {P, Suc npre} c @ c'"
          apply(auto)
      next
        case False
        then show ?thesis sorry
      qed

      then show ?case using HTcE[OF Suc.prems] HTE[OF NP']
    qed


    have Conc' : "guardedc gs Q c'"
    proof
      fix m :: "('a, 'b) control"
      assume Qm : "Q (payload m)"
      assume Cm : "s_cont m = Inl c'"
      show "safec gs m" using X Qm Cm
      proof(induction npre arbitrary: c' m npre)
        case 0

        have Safe0 : "safe_for gs m 0"
          using guardedD[OF `|gs| {Q, 0} c'` `Q (payload m)` `s_cont m = Inl c'`] by simp

        show ?case
        proof(cases c')
          case Nil
          then show ?thesis 
        next
          case (Cons a list)
          then show ?thesis sorry
        qed

        then show ?case 
      next
        case (Suc npost)

        have "|gs| {Q, npost} c'"
        proof
          fix m' :: "('a, 'b) control"
          assume Qm' : "Q (payload m')"
          assume Cm' : "s_cont m' = Inl c'"

          have Conc' : "safe_for gs m' (Suc npost)"
            using guardedD[OF `|gs| {Q, Suc npost} c'` Qm' Cm']
            by auto

          show "safe_for gs m' npost" 
            using safe_for_weaken[OF Conc', of npost] by auto
        qed

        then show ?case using Suc.IH[OF `|gs| {Q, npost} c'` Suc.prems(2) Suc.prems(3)] by auto
      qed
          using guardedD[OF `|gs| {Q, Suc npost} c'` `Q (payload m)` `s_cont m = Inl c'`]
      qed

proof-
  show "\<forall> npre . \<exists> npost . |gs| {-P, npre-} c {-Q, npost-}"
  proof(step)
    fix npre

    show "\<exists>npost. |gs| {-P, npre-} c {-Q, npost-}" 

    proof(induction npre arbitrary: c)
      case 0

      have "|gs| {-P, 0-} c {-Q, 0-}"
      proof
        fix c'
        show "|gs| {P, 0} c @ c'"
        proof
          fix m :: "('a, 'b) control"

          assume Pm : "P (payload m)"
          assume Cm : "s_cont m = Inl (c @ c')"

          show "safe_for gs m 0" sorry (* case analysis *)
        qed
      qed

      then show ?case by blast
    next
      case (Suc npre)

      obtain npost' where NP' : "|gs| {-P, npre-} c {-Q, npost'-}"
        using Suc by blast

      show ?case unfolding HT_def
      proof(cases "guardedc gs Q c")
        case False

        then obtain mbad where Mbad : "Q (payload mbad)" "s_cont mbad = Inl c" "\<not> safec gs mbad"
          unfolding guardedc_def
          by blast

        then obtain mbad' where Mbad' : "sem_exec_p gs mbad mbad'" "\<not> imm_safe gs mbad'"
          unfolding safec_def by blast

        obtain nbad where Nbad : "sem_exec_c_p gs mbad nbad mbad'"
          using exec_p_imp_exec_c_p[OF Mbad'(1)] by blast

        show "\<exists>a. \<forall>c'. |gs| {Q, a} c' \<longrightarrow> |gs| {P, Suc npre} c @ c'"
          apply(auto)
      next
        case False
        then show ?thesis sorry
      qed

      then show ?case using HTcE[OF Suc.prems] HTE[OF NP']
    qed

    show "|gs| {P, npre} c @ c'"

    have Conc' : "\<forall> npost . |gs| {-P, npre-} c {-Q, npost-}"
    proof
      fix npost
      show "|gs| {-P, npre-} c {-Q, npost-}"
      proof
        fix c'
        assume Guard : "|gs| {Q, npost} c'"

        have "guardedc gs Q c'"
        proof
          fix m :: "('a, 'b) control"

          assume Qm : "Q (payload m)"
          assume Cm : "s_cont m = Inl c'"

          show "safec gs m"
          proof
            fix m'
            assume Exec :"sem_exec_p gs m m'"

            obtain n where Exec' : "sem_exec_c_p gs m n m'"
              using exec_p_imp_exec_c_p[OF Exec] by blast

            show "imm_safe gs m'" using guardedD[OF Guard Qm Cm]
(* problem - what if n > npre? *)

        show "|gs| {P, npre} c @ c'"
        proof
          fix m :: "('a, 'b) control"
          assume Pm : "P (payload m)"
          assume Cm : "s_cont m = Inl (c @ c')" 
          show "safe_for gs m npre"
            using HTcE[OF H]

            sorry
        qed
      qed
   qed
*)

end