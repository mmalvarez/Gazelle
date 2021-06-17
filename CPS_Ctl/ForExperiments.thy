theory ForExperiments

(* Trying to explore/clarify the conditions under which
we can obtain a while rule *)

imports "./ImpCtl"

begin

lemma WhileHelper :
  assumes H0 : "gs = \<lparr> s_sem = pcomps' fs \<rparr>"
  (*assumes H1 : "seq_sem_l_gen lfts \<in> set fs" *)
  assumes HF : "f = imp_sem_l_gen lfts"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hnemp : "g \<in> set fs"
  assumes Hdom_while : "(f \<downharpoonleft> (set fs) SwhileC')"
  assumes Hdom_skip : "(f \<downharpoonleft> (set fs) Sskip')"
  assumes Hwhile : "lfts SwhileC' = SwhileC"
  assumes Hskip : "lfts Sskip' = ImpCtl.Sskip"
  (* TODO: generalize. these should be expressed using valid-sets *)
  assumes Cond : "get_cond (payload st) = Some True"
  assumes Cont : "s_cont st = Inl ((G SwhileC' [G Sskip' l]) # c') \<or>
                  s_cont st = Inl ((G Sskip' l) # (G SwhileC' [G Sskip' l]) # c')"
  assumes Exec : "sem_exec_p gs st st'"

shows "payload st' = payload st \<and>
       (s_cont st' = Inl ((G SwhileC' [G Sskip' l]) # c') \<or>
        s_cont st' = Inl ((G Sskip' l) # (G SwhileC' [G Sskip' l]) # c'))"
  using Exec Cond Cont unfolding sem_exec_p_def
proof(induction arbitrary: c' rule:converse_rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step y z)

  show ?case
  proof(cases "sem_step gs y")
    case (Inr bad)

    then have False using H0 step.prems
      by(auto simp add: sem_step_def)

    then show ?thesis by auto
  next
    case (Inl y')

    have Zeq : "y' = z"
      using Inl step.hyps unfolding sem_step_p_eq by auto

    consider
      (CaseA) "s_cont y = Inl (G SwhileC' [G Sskip' l] # c')" |
      (CaseB) "s_cont y = Inl (G Sskip' l # G SwhileC' [G Sskip' l] # c')"
      using step.prems by auto
    then show ?thesis
    proof cases
      case CaseA

      then have F_eq : "sem_step \<lparr> s_sem = f \<rparr> y = Inl y'"
        using sym[OF dominant_pcomps'[OF Hpres Hnemp Hdom_while]] step.prems Inl H0
        by(auto simp add: sem_step_def)


      have C1 : "payload z = payload y"
        using Hwhile H0 F_eq CaseA step.prems(1) unfolding HF Zeq
        by(cases y; cases y'; 
            auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
            schem_lift_defs 
            merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
            get_cond_def
            split: md_prio.splits md_triv.splits option.splits)

      hence C2 : "get_cond (payload z) = Some True" using step.prems by auto

      have "s_cont z = Inl (G Sskip' l # G SwhileC' [G Sskip' l] # c')"
        using Hwhile H0 F_eq CaseA step.prems(1) unfolding HF Zeq
        by(cases y; cases y'; 
            auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
            schem_lift_defs 
            merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
            get_cond_def
            split: md_prio.splits md_triv.splits option.splits)

      hence C3 : "s_cont z = Inl (G SwhileC' [G Sskip' l] # c') \<or>
        s_cont z = Inl (G Sskip' l # G SwhileC' [G Sskip' l] # c')"
        by auto

      then show ?thesis using step.IH[OF C2 C3] CaseA unfolding C1
        by auto
    next
      case CaseB

      then have F_eq : "sem_step \<lparr> s_sem = f \<rparr> y = Inl y'"
        using sym[OF dominant_pcomps'[OF Hpres Hnemp Hdom_skip]] step.prems Inl H0
        by(auto simp add: sem_step_def)


      have C1 : "payload z = payload y"
        using Hwhile H0 F_eq CaseB step.prems(1) unfolding HF Zeq
        by(cases y;
            auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
            schem_lift_defs 
            merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
            get_cond_def
            split: md_prio.splits md_triv.splits option.splits)

      hence C2 : "get_cond (payload z) = Some True" using step.prems by auto

      have C3' : "s_cont z = Inl (G SwhileC' [G Sskip' l] # c')"
        using Hskip H0 F_eq CaseB step.prems(1) unfolding HF Zeq
        by(cases y;
            auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
            schem_lift_defs 
            merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
            get_cond_def
            split: md_prio.splits md_triv.splits option.splits)

      hence C3 : "s_cont z = Inl (G SwhileC' [G Sskip' l] # c') \<or>
        s_cont z = Inl (G Sskip' l # G SwhileC' [G Sskip' l] # c')"
        by auto

      then show ?thesis using step.IH[OF C2 C3] CaseB C3' unfolding C1
        by(auto)
    qed
  qed
qed

lemma WhileHelper1 :
  assumes H0 : "gs = \<lparr> s_sem = pcomps' fs \<rparr>"
  (*assumes H1 : "seq_sem_l_gen lfts \<in> set fs" *)
  assumes HF : "f = imp_sem_l_gen lfts"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hnemp : "g \<in> set fs"
  assumes Hdom_while : "(f \<downharpoonleft> (set fs) SwhileC')"
  assumes Hdom_skip : "(f \<downharpoonleft> (set fs) Sskip')"
  assumes Hwhile : "lfts SwhileC' = SwhileC"
  assumes Hskip : "lfts Sskip' = ImpCtl.Sskip"
  (* TODO: generalize. these should be expressed using valid-sets *)
  assumes Cond : "\<And> st . P1 st \<Longrightarrow> get_cond st = Some True"

  assumes Htrue : "|gs| {- P1 -} [body]
                        {- P1 -}"
shows "|gs| {- P1  -} replicate n body @ [(G SwhileC' [G Sskip' l])] {- (\<lambda> st . False ) -}"
proof(induction n arbitrary: )
  case 0

  have "|gs| {-P1-} [G SwhileC' [G Sskip' l]] {-C False-}"
  proof
    fix c'
    assume Hc' : "|gs| {\<lambda> x. False} c'"

    show "|gs| {P1} [G SwhileC' [G Sskip' l]] @ c'"
    proof
      fix m :: "('a, 'b) state"
      assume Pay : "P1 (payload m)" 
      assume Cont : "s_cont m = Inl ([G SwhileC' [G Sskip' l]] @ c')"

      hence Cont' : "s_cont m = Inl (G SwhileC' [G Sskip' l] # c')" by auto

      have Cond : "get_cond (payload m) = Some True"
        using Cond[OF Pay] by auto

      show "safe gs m"
      proof
        fix m' :: "('a, 'b) state"
        assume Exec : "sem_exec_p gs m m'"

        have Cont'' : "s_cont m = Inl (G SwhileC' [G Sskip' l] # c') \<or>
           s_cont m = Inl (G Sskip' l # G SwhileC' [G Sskip' l] # c')"
          using disjI1[OF Cont'] by auto

        have Cases : "(s_cont m' = Inl (G SwhileC' [G Sskip' l] # c') \<or>
         s_cont m' = Inl (G Sskip' l # G SwhileC' [G Sskip' l] # c'))"
          using WhileHelper[OF H0 HF Hpres Hnemp Hdom_while Hdom_skip Hwhile Hskip Cond Cont'' Exec]
          by auto

        consider (CaseA) "s_cont m' = Inl (G SwhileC' [G Sskip' l] # c')" |
                 (CaseB) "s_cont m' = Inl (G Sskip' l # G SwhileC' [G Sskip' l] # c')"
          using Cases by auto

        then show "imm_safe gs m'" 
        proof cases
          case CaseA

          then show ?thesis
          proof(cases "sem_step gs m'")
            case (Inr bad)
            then have False using H0 CaseA
              by(auto simp add: sem_step_def)
        
            then show ?thesis by auto
          next
            case (Inl m'')
            then show ?thesis 
              unfolding imm_safe_def sem_step_p_eq by blast
          qed
        next
          case CaseB
          then show ?thesis
          proof(cases "sem_step gs m'")
            case (Inr bad)
            then have False using H0 CaseB
              by(auto simp add: sem_step_def)
        
            then show ?thesis by auto
          next
            case (Inl m'')
            then show ?thesis 
              unfolding imm_safe_def sem_step_p_eq by blast
          qed
        qed
      qed
    qed
  qed

  thus ?case by auto
next
    
  case (Suc n)

  have "|gs| {-P1-} body # replicate ( n) body @ [G SwhileC' [G Sskip' l]] {-C False-}"
    using HCat[OF Htrue Suc.IH] by auto

  then show ?case by auto
qed

(* use notion of absorption, again from Appel paper. 
"separation logic for small step cminor"
*)

type_synonym 'full only_control =
"'full gensyn list md_triv option md_prio * String.literal md_triv option md_prio"

(* do we need to partition out the continuation from the state here? *)
definition absorbs :: "('syn, 'mstate) semc \<Rightarrow> 'syn gensyn \<Rightarrow> 'mstate \<Rightarrow> nat \<Rightarrow> bool" where
"absorbs gs st m n =
  (\<forall> j . j \<le> n \<longrightarrow> 
    (\<exists> prefix st' .  
      (\<forall> k m_full .
        s_cont m_full = Inl (st # k) \<longrightarrow> 
        payload m_full = m \<longrightarrow>
        (\<exists> m_full' . 
          sem_exec_c_p gs m_full j m_full' \<and> 
          payload m_full' = st' \<and>
          s_cont m_full' = Inl (prefix @ k)))))"

lemma absorbs_0 :
  "absorbs gs st m 0"
proof-

  have 0: "(\<And> a aa k . s_cont (a, aa, m) = Inl (st # k) \<Longrightarrow>
        \<exists>ab ac.
          sem_exec_c_p gs (a, aa, m) 0 (ab, ac, m) \<and>
          s_cont (ab, ac, m) = Inl (st # k)) \<Longrightarrow> absorbs gs st m 0"
    unfolding absorbs_def
    apply(auto)
    apply(rule_tac x = "[st]" in exI)
    apply(rule_tac x = m in exI)
    apply(auto)
    done

  have 1: "\<And> a aa k . s_cont (a, aa, m) = Inl (st # k) \<Longrightarrow>
        \<exists>ab ac.
          sem_exec_c_p gs (a, aa, m) 0 (ab, ac, m) \<and>
          s_cont (ab, ac, m) = Inl (st # k)"
  proof-
    fix a aa k
    assume H: "s_cont (a, aa, m) = Inl (st# k)"

    show "\<exists>ab ac.
          sem_exec_c_p gs (a, aa, m) 0 (ab, ac, m) \<and>
          s_cont (ab, ac, m) = Inl (st # k)"
      using sem_exec_c_p.intros(1)[of gs "(a, aa, m)"] H
      by auto
  qed

  show "absorbs gs st m 0" using 0 1
    by auto
qed


lemma absorbs_less :
  assumes H : "absorbs gs st m (Suc n)"
  shows "absorbs gs st m n" using H
  unfolding absorbs_def
proof(step)
  fix j

  assume H0 : "\<forall>j\<le>Suc n.
            \<exists>prefix st'.
               \<forall>k m_full.
                  s_cont m_full = Inl (st # k) \<longrightarrow>
                  payload m_full = m \<longrightarrow> (\<exists>m_full'. sem_exec_c_p gs m_full j m_full' \<and> payload m_full' = st' \<and> s_cont m_full' = Inl (prefix @ k))"
  assume H1: "j \<le> n"

  have H0' : "\<exists>prefix st'.
               \<forall>k m_full.
                  s_cont m_full = Inl (st # k) \<longrightarrow>
                  payload m_full = m \<longrightarrow> (\<exists>m_full'. sem_exec_c_p gs m_full j m_full' \<and> payload m_full' = st' \<and> s_cont m_full' = Inl (prefix @ k))"
    using H0 H1
    by auto

  then obtain prefix st' where Hpfx :
    "\<And> k m_full . s_cont m_full = Inl (st # k) \<Longrightarrow>
                  payload m_full = m \<Longrightarrow> (\<exists>m_full'. sem_exec_c_p gs m_full j m_full' \<and> payload m_full' = st' \<and> s_cont m_full' = Inl (prefix @ k))"
    by blast

  then show " \<exists>prefix st'.
            \<forall>k m_full.
               s_cont m_full = Inl (st # k) \<longrightarrow> payload m_full = m \<longrightarrow> (\<exists>m_full'. sem_exec_c_p gs m_full j m_full' \<and> payload m_full' = st' \<and> s_cont m_full' = Inl (prefix @ k))"
    by blast
qed
  

lemma absorbs_at_most :
  assumes H: "\<not> absorbs gs st m n"
  shows "\<exists> i . i < n \<and> absorbs gs st m i \<and> \<not> absorbs gs st m (Suc i)" using H
proof(induction n arbitrary: m)
  case 0

  then have False using absorbs_0[of gs st m] by auto

  then show ?case by auto
next
  case (Suc n)

  then show ?case
  proof(cases "absorbs gs st m n")
    case False

    have "\<exists>i<n. absorbs gs st m i \<and> \<not> absorbs gs st m (Suc i)"
      using Suc.IH[OF False] by auto

    then obtain i where Li : "i < n" and Ai : "absorbs gs st m i" and Nai : "\<not> absorbs gs st m (Suc i)"
      by blast

    have C1 : "i < Suc n" using Li by auto
  
    show ?thesis using C1 Ai Nai by blast
  next
    case True

    have C1 : "n < Suc n" by auto

    show ?thesis using Suc.prems C1 True by blast
  qed
qed

lemma HWhile_gen0 :
  assumes H0 : "gs = \<lparr> s_sem = pcomps' fs \<rparr>"
  (*assumes H1 : "seq_sem_l_gen lfts \<in> set fs" *)
  assumes HF : "f = imp_sem_l_gen lfts"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hnemp : "g \<in> set fs"
  assumes Hdom_while : "(f \<downharpoonleft> (set fs) SwhileC')"
  assumes Hdom_skip : "(f \<downharpoonleft> (set fs) Sskip')"
  assumes Hwhile : "lfts SwhileC' = SwhileC"
  assumes Hskip : "lfts Sskip' = ImpCtl.Sskip"
  (* TODO: generalize. these should be expressed using valid-sets *)
  assumes P1_valid : "\<And> st.  P1 st \<Longrightarrow> get_cond st = Some True"
  assumes Htrue : "|gs| {- P1 -} [body]
                        {- P1 -}"
  shows "|gs| {- P1  -} [(G Swhile'C [body])] {- (\<lambda> st . False ) -}"
proof

  fix c'
  assume Guard : "|gs| {\<lambda>st. False } c'"

  show "|gs| {P1} [(G Swhile'C [body])] @ c'"
  proof
    fix m :: "('a, 'b) state"
    assume P : "P1 (payload m)"

    assume Cont : "s_cont m = Inl (([G Swhile'C [body]]) @ c')"

    hence Cont' : "s_cont m = Inl ((G Swhile'C [body]) # c')"
      by auto

    show "safe gs m"
    proof
      fix m' :: "('a, 'b) state"

      assume Exec : "sem_exec_p gs m m'"

      obtain n where N : "sem_exec_c_p gs m n m'"
        using exec_p_imp_exec_c_p[OF Exec]
        by auto

      have Unfold : "|gs| {-P1-} replicate n body @
                [G SwhileC' [G Sskip' []]] {-C False-}"
        using WhileHelper1[OF H0 HF Hpres Hnemp Hdom_while Hdom_skip Hwhile Hskip
            P1_valid _ ] Htrue
        by fastforce

      have Guard' : "|gs| {P1} (replicate n body @ [G SwhileC' [G Sskip' []]]) @ c'" 
        using HTE[OF Unfold Guard] by auto


      (* gross low-level deconstruction of m to build a new state *)
      obtain m1 m2 m3 m4 m5 where Mcomp : "m = (m1, m2, m3, m4, m5)"
        by(cases m; auto)

      obtain malt :: "('a, 'b) state" where Malt :
        "malt = (mdp 0 (Some (mdt (replicate n body @ [G SwhileC' [G Sskip' []]] @ c'))), 
                 mdp 0 None,
                 m3,
                 m4,
                 m5)" by simp

      have Malt_pl : "payload malt = payload m" using Malt Mcomp by auto

      hence Malt_P : "P1 (payload malt)" using P unfolding Malt_pl by auto

      have Malt_cont : "s_cont malt = Inl (((replicate n body @ [G SwhileC' [G Sskip' []]]) @ c'))"
        using Malt by (auto simp add: s_cont_def)
        
      have Malt_safe : "safe gs malt" using guardedD[OF Guard' Malt_P Malt_cont] by auto

      show "imm_safe gs m'" using N
      proof(cases rule: sem_exec_c_p.cases)
        case Excp_0

        have "imm_safe gs m" sorry

        then show ?thesis using Excp_0 by auto
      next
        (* We are just doing this to get the fact that n > 0 *)
        case (Excp_Suc mz2 n')
   
        have Malt_cont' : "s_cont malt = Inl (body # ((replicate n' body @ [G SwhileC' [G Sskip' []]]) @ c'))"
          using Excp_Suc Malt_cont
          by auto

        show "imm_safe gs m'"
        proof(cases "absorbs gs body (payload m) n")
          case True
  
          have "\<exists>prefix st'.
                \<forall>k m_full.
                   s_cont m_full = Inl (body # k) \<longrightarrow>
                   payload m_full = payload m \<longrightarrow> (\<exists>m_full'. sem_exec_c_p gs m_full n m_full' \<and> payload m_full' = st' \<and> s_cont m_full' = Inl (prefix @ k))"
            using True unfolding absorbs_def by auto
  
  
          then obtain prefix and m'x :: "(bool md_triv option md_prio * int md_triv option md_prio * 'b)" where 
              Absorbed : "\<forall>k m_full.
                   s_cont m_full = Inl (body # k) \<longrightarrow>
                   payload m_full = payload m \<longrightarrow> (\<exists>m_full'. sem_exec_c_p gs m_full n m_full' \<and> payload m_full' = m'x \<and> s_cont m_full' = Inl (prefix @ k))"
            by blast
  
          then obtain malt' ::"('a, 'b) state"  where
            "(sem_exec_c_p gs malt n malt' \<and> payload malt' = m'x \<and> s_cont malt' = Inl (prefix @ ((replicate n' body @ [G SwhileC' [G Sskip' []]]) @ c')))"
            using Malt_cont' Malt_pl
            by blast

          have "imm_safe gs malt'" sorry (* since malt is known to be safe *)

          obtain m2 where M2 : "sem_step_p gs m m2" and M2_cont : "s_cont m2 = Inl (body # ([G Swhile'C [body]] @ c'))" and M2_pay : "payload m2 = payload m"
            sorry

          then obtain m2' ::"('a, 'b) state" where "sem_exec_c_p gs m2 n m2' \<and> payload m2' = m'x \<and> s_cont m2' = Inl (prefix @ ([G Swhile'C [body]] @ c'))"
            using M2_cont M2_pay Absorbed
            by blast

          hence M2'_exec : "sem_exec_c_p gs m2 n m2' " by auto

          have "imm_safe gs m2'" (* since prefix will be enough to guarantee safety *) sorry

          have Exec_m2' : "sem_exec_c_p gs m (n+1) m2'" using sem_exec_c_p.intros(2)[OF M2 M2'_exec] by auto

          have Duh : "n \<le> n + 1" by simp

          obtain m'_copy where M'_copy1 : "sem_exec_c_p gs m n m'_copy" and M'_copy2 : "sem_exec_c_p gs m'_copy (n + 1 - n) m2'" using exec_c_p_split[OF Exec_m2' Duh] 
            by auto

          have M'_copy_m' : "m'_copy = m'" using exec_c_p_determ[OF N M'_copy1]
            by auto

          have Last_step : "sem_exec_c_p gs m'_copy (1) m2'" using M'_copy2 by auto

          hence "sem_step_p gs m' m2'"
            using Excp_1'[OF Last_step] unfolding M'_copy_m' by auto
  
          then show ?thesis unfolding imm_safe_def by blast
        next
          case False

          obtain i where
            Ilt : "i < n" and Iabs : "absorbs gs body (payload m) i" and Imax : "\<not> absorbs gs body (payload m) (Suc i)"
            using absorbs_at_most[OF False] by blast

          then show ?thesis sorry
        qed
      qed
    qed
  qed
qed
(* idea: after n steps we are either in body; loop or just loop.
 either way though we're stuck. *)

    proof(induction n arbitrary: c')
      case 0
      then show ?case by auto
    next
      case (Suc n1)

      show ?thesis using Suc

      have "|gs| {P1} replicate 1 (G SwhileC' [body]) @ c'"
      proof
        fix mx :: "('a, 'b) state"

        assume X1 : "P1 (payload mx)" 
        assume X2 : "s_cont mx = Inl (replicate 1 (G SwhileC' [body]) @ c')"

        show "safe gs mx" using Suc.IH Suc.prems


      have Cont' : "s_cont m = Inl ((replicate (n1) (G SwhileC' [body])) @ c')"
        using Suc
        by(simp add: replicate_append_same)

      have "|gs| {P1} [G SwhileC' [body]] @ c'"
        using Suc.IH Suc.prems

      show ?case using Suc.prems Suc.IH[OF _ Cont']

        


      proof(cases n')
        case Z' : 0

        then show ?thesis sorry (* should be easy i think *)
      next
        case Suc' : (Suc n'1)

        have Cont' : "s_cont m = Inl (replicate (n'1) (G SwhileC' [body]) @ ((G SwhileC' [body]) # c'))"
          using Suc Suc'
          by(simp add: replicate_append_same)


        have "|gs| {\<lambda>st. P1 st } ((G SwhileC' [body]) # c')"
        proof
          fix mx :: "('a, 'b) state"

          assume HX : "P1 (payload mx)"

          assume ContX : "s_cont mx = Inl (G SwhileC' [body] # c')"
          hence ContX' : "s_cont mx = Inl (replicate 1 (G SwhileC' [body]) @ c')" by auto

          have "n'1 < n1" using Suc.prems Suc' by auto

          show "safe gs mx" using Suc.IH Suc.prems

      show ?case using Suc

    qed


      fix m'
      assume Exec : "sem_exec_p gs m m'"
      show "imm_safe gs m'"

      proof(cases "(sem_step gs m)")
        case (Inr bad)
  
        then have False using Cont H0
          by(auto simp add: sem_step_def)
  
        then show ?thesis by auto
      next
        case (Inl m2)
  
        have F_eq : "sem_step \<lparr> s_sem = f \<rparr> m = Inl m2"
          using sym[OF dominant_pcomps'[OF Hpres Hnemp Hdom]] Cont Inl H0
          by(simp add: sem_step_def)

        (* this will need to be shown using valid-sets. *)
        have M_valid : "\<And> p . fst (payload m) \<noteq> mdp p None" using P1_valid[OF P]
          by(auto simp add: get_cond_def split:prod.splits)

        show ?thesis
        proof(cases "get_cond (payload m)")
          case None

          then have False using P1_valid[OF P]
            by(auto simp add: get_cond_def split: prod.splits md_prio.splits md_triv.splits option.splits)

          then show ?thesis by auto

        next
          case Some : (Some cnd)
          then show ?thesis 
          proof(cases cnd)
            case True

            have M2_cont : "s_cont m2 = Inl ([body, G SwhileC' [body]] @ c')"
              using Inl True Cont Some Hsyn F_eq M_valid  unfolding HF
              by(cases m2; cases m; 
                  auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
                  schem_lift_defs 
                  merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
                  get_cond_def
                  split: md_prio.splits md_triv.splits option.splits)

            show ?thesis
              using HTE[OF Htrue]

              sorry
          next

            case False
            then show ?thesis sorry
          qed

          proof(cases "sem_step gs m2")
            case (Inr bad)

            then have False using Cont2 H0
              by(auto simp add: sem_step_def)

            then show ?thesis by auto

          next
            case (Inl mp2')

            have F_eq' : "sem_step \<lparr> s_sem = f \<rparr> mp2 = Inl mp2'"
              using sym[OF dominant_pcomps'[OF Hpres Hnemp Hdom]] Cont2 Inl H0
              by(simp add: sem_step_def)

            have Mp2'_p2 : "P2 (payload mp2')"
              using Cont2 Hsyn H0 MP2 F_eq' P2_valid[OF MP2] Some' unfolding HF
              by(cases mp2; cases mp2'; 
                  auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
                  schem_lift_defs 
                  merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
                  get_cond_def
                  split: md_prio.splits md_triv.splits option.splits)

            show ?thesis
            proof(cases cnd)
              case True
        
              have Mp2'_cond : "get_cond (payload mp2') = Some True" 
                using Cont2 Hsyn H0 MP2 F_eq' P2_valid[OF MP2] True Some' unfolding HF
                by(cases mp2; cases mp2'; 
                    auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
                    schem_lift_defs 
                    merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
                    get_cond_def
                    split: md_prio.splits md_triv.splits option.splits)

              have Mp2'_p2_true :  "P2 (payload mp2') \<and> get_cond (payload mp2') = Some True"
                using Mp2'_p2 Mp2'_cond
                by auto

      have CM' : "s_cont m' = Inl ([body] @ ([ G SwhileC' [body]] @ c'))" 
        using Cont Hsyn F_eq unfolding HF
        by(cases m; cases m'; auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
           schem_lift_defs 
          merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def
          split: md_prio.splits md_triv.splits option.splits)

      (* this will need to be shown using valid-sets. *)
      have M'_valid : "\<And> p . fst (payload m) \<noteq> mdp p None" using P1_valid[OF M]
        by(auto simp add: get_cond_def split:prod.splits)

      have Sm' : "payload m = payload m'"
        using CM Hsyn F_eq M'_valid  unfolding HF
        by(cases m; cases m'; auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
           schem_lift_defs 
          merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
          split: md_prio.splits md_triv.splits option.splits)

      hence P1sm' : "P1 (payload m')" using M unfolding Sm' by auto

      (* next: step to the end of cond. *)

      have Sub : "|gs| {P2} [G Sif' [body]] @ c'"
      proof
        fix mp2 :: "('a, 'b) state"

        assume MP2 : "P2 (payload mp2)"

        assume Cont2 : "s_cont mp2 = Inl ([G Sif' [body]] @ c')"

        show "safe gs mp2"
        proof(cases "get_cond (payload mp2)")
          case None

          then have False using P2_valid[OF MP2]
            by(auto simp add: get_cond_def split: prod.splits md_prio.splits md_triv.splits option.splits)
          then show ?thesis by auto

        next
          case Some' : (Some cnd)
          then show ?thesis 
          proof(cases "sem_step gs mp2")
            case (Inr bad)

            then have False using Cont2 H0
              by(auto simp add: sem_step_def)

            then show ?thesis by auto

          next
            case (Inl mp2')

            have F_eq' : "sem_step \<lparr> s_sem = f \<rparr> mp2 = Inl mp2'"
              using sym[OF dominant_pcomps'[OF Hpres Hnemp Hdom]] Cont2 Inl H0
              by(simp add: sem_step_def)

            have Mp2'_p2 : "P2 (payload mp2')"
              using Cont2 Hsyn H0 MP2 F_eq' P2_valid[OF MP2] Some' unfolding HF
              by(cases mp2; cases mp2'; 
                  auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
                  schem_lift_defs 
                  merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
                  get_cond_def
                  split: md_prio.splits md_triv.splits option.splits)

            show ?thesis
            proof(cases cnd)
              case True
        
              have Mp2'_cond : "get_cond (payload mp2') = Some True" 
                using Cont2 Hsyn H0 MP2 F_eq' P2_valid[OF MP2] True Some' unfolding HF
                by(cases mp2; cases mp2'; 
                    auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
                    schem_lift_defs 
                    merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
                    get_cond_def
                    split: md_prio.splits md_triv.splits option.splits)

              have Mp2'_p2_true :  "P2 (payload mp2') \<and> get_cond (payload mp2') = Some True"
                using Mp2'_p2 Mp2'_cond
                by auto

              have Mp2'_cont : "s_cont mp2' = Inl ([body] @ c')"
                using Cont2 Hsyn H0 MP2 F_eq' P2_valid[OF MP2] True Some' unfolding HF
                by(cases mp2; cases mp2'; 
                    auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
                    schem_lift_defs 
                    merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
                    get_cond_def
                    split: md_prio.splits md_triv.splits option.splits)

              have Mp2'_safe : "safe gs mp2'"
                using guardedD[OF Gtrue Mp2'_p2_true Mp2'_cont] by auto

              show ?thesis
              proof
                fix mz
                assume Exec : "sem_exec_p gs mp2 mz"

                show "imm_safe gs mz" using Exec unfolding sem_exec_p_def
                proof(cases rule: rtranclp.cases)
                  case rtrancl_refl

                  then have "(\<exists>m'. sem_step gs mz = Inl m')"
                    using Inl unfolding imm_safe_def sem_step_p_eq
                    by(cases mp2'; auto)

                  then show ?thesis unfolding imm_safe_def sem_step_p_eq by auto
                next
                  case (rtrancl_into_rtrancl b)

                  have Step : "sem_step_p gs mp2 mp2'" using Inl
                    unfolding sem_step_p_eq
                    by auto
        
                  have Exec_final : "sem_exec_p gs mp2' mz"
                    using rtranclp_bisect1
                      [OF sem_step_determ rtrancl_into_rtrancl(1)
                          Step rtrancl_into_rtrancl(2)]
                    unfolding sem_exec_p_def
                    by auto
        
                  show ?thesis using safeD[OF Mp2'_safe Exec_final] by auto 
                qed
              qed

            next
              case False

              have Mp2'_cond : "get_cond (payload mp2') = Some False" 
                using Cont2 Hsyn H0 MP2 F_eq' P2_valid[OF MP2] False Some' unfolding HF
                by(cases mp2; cases mp2'; 
                    auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
                    schem_lift_defs 
                    merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
                    get_cond_def
                    split: md_prio.splits md_triv.splits option.splits)

              have Mp2'_p2_false :  "P2 (payload mp2') \<and> get_cond (payload mp2') = Some False"
                using Mp2'_p2 Mp2'_cond
                by auto

              have Mp2'_cont : "s_cont mp2' = Inl ([] @ c')"
                using Cont2 Hsyn H0 MP2 F_eq' P2_valid[OF MP2] False Some' unfolding HF
                by(cases mp2; cases mp2'; 
                    auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
                    schem_lift_defs 
                    merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
                    get_cond_def
                    split: md_prio.splits md_triv.splits option.splits)

              have Mp2'_safe : "safe gs mp2'"
                using guardedD[OF Gfalse Mp2'_p2_false Mp2'_cont] by auto

              show ?thesis
              proof
                fix mz
                assume Exec : "sem_exec_p gs mp2 mz"

                show "imm_safe gs mz" using Exec unfolding sem_exec_p_def
                proof(cases rule: rtranclp.cases)
                  case rtrancl_refl

                  then have "(\<exists>m'. sem_step gs mz = Inl m')"
                    using Inl unfolding imm_safe_def sem_step_p_eq
                    by(cases mp2'; auto)

                  then show ?thesis unfolding imm_safe_def sem_step_p_eq by auto
                next
                  case (rtrancl_into_rtrancl b)

                  have Step : "sem_step_p gs mp2 mp2'" using Inl
                    unfolding sem_step_p_eq
                    by auto
        
                  have Exec_final : "sem_exec_p gs mp2' mz"
                    using rtranclp_bisect1
                      [OF sem_step_determ rtrancl_into_rtrancl(1)
                          Step rtrancl_into_rtrancl(2)]
                    unfolding sem_exec_p_def
                    by auto
        
                  show ?thesis using safeD[OF Mp2'_safe Exec_final] by auto 
                qed
              qed
            qed
          qed
        qed
      qed

      have Guard' : "|gs| {P1} [cond] @ ([G Sif' [body]] @ c')"
        using HTE[OF Hcond Sub] by auto

      have Safe' : "safe gs m'" using guardedD[OF Guard' P1sm' CM'] by auto

      show "safe gs m"
      proof
        fix mz

        assume Z: "sem_exec_p gs m mz"

        then show "imm_safe gs mz" unfolding sem_exec_p_def
        proof(cases rule: rtranclp.cases)
          case rtrancl_refl

          then have "(\<exists>m'. sem_step gs mz = Inl m')"
            using Inl unfolding imm_safe_def sem_step_p_eq
            by(cases m'; auto)

          then show ?thesis using Inl unfolding imm_safe_def sem_step_p_eq
            by(auto)
        next
          case (rtrancl_into_rtrancl b)

          have Step : "sem_step_p gs m m'" using Inl
            unfolding sem_step_p_eq
            by auto

          have Exec_final : "sem_exec_p gs m' mz"
            using rtranclp_bisect1
              [OF sem_step_determ rtrancl_into_rtrancl(1)
                  Step rtrancl_into_rtrancl(2)]
            unfolding sem_exec_p_def
            by auto

          show ?thesis using safeD[OF Safe' Exec_final] by auto
        qed
      qed
    qed
  qed
qed

end