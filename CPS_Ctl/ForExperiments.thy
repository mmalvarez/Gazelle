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
      obtain m1 m2xx m3 m4 m5 where Mcomp : "m = (m1, m2xx, m3, m4, m5)"
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

      obtain m2 where M2 : "sem_step_p gs m m2" and M2_cont : "s_cont m2 = Inl (body # ([G Swhile'C [body]] @ c'))" and M2_pay : "payload m2 = payload m"
        sorry

      obtain maltb :: "('a, 'b) state" where Maltb :
        "maltb = (mdp 0 (Some (mdt (body # []))), 
                 mdp 0 None,
                 m3,
                 m4,
                 m5)" by simp

      have Maltb_pl : "payload maltb = payload m" using Maltb Mcomp by auto

      hence Maltb_P : "P1 (payload maltb)" using P unfolding Maltb_pl by auto

      have Maltb_cont : "s_cont maltb = Inl (body # [])"
        using Maltb by (auto simp add: s_cont_def)


      show "imm_safe gs m'" using N
      proof(cases rule: sem_exec_c_p.cases)
        case Excp_0

        have "imm_safe gs m" sorry

        then show ?thesis using Excp_0 by auto
      next
        (* We are just doing this to get the fact that n > 0. or should be we doing an actual induction? *)
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

          obtain m2' ::"('a, 'b) state" where "sem_exec_c_p gs m2 n m2' \<and> payload m2' = m'x \<and> s_cont m2' = Inl (prefix @ ([G Swhile'C [body]] @ c'))"
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

          have M2_cont' : "s_cont m2 = Inl (body # ([G Swhile'C [body]] @ c'))" using M2_cont by auto

          have "\<exists>prefix st'.
                \<forall>k m_full.
                   s_cont m_full = Inl (body # k) \<longrightarrow>
                   payload m_full = payload m \<longrightarrow> (\<exists>m_full'. sem_exec_c_p gs m_full i m_full' \<and> payload m_full' = st' \<and> s_cont m_full' = Inl (prefix @ k))"
            using Iabs unfolding absorbs_def by auto
  
  
          then obtain prefix and m'x :: "(bool md_triv option md_prio * int md_triv option md_prio * 'b)" where 
              Absorbed : "\<forall>k m_full.
                   s_cont m_full = Inl (body # k) \<longrightarrow>
                   payload m_full = payload m \<longrightarrow> (\<exists>m_full'. sem_exec_c_p gs m_full i m_full' \<and> payload m_full' = m'x \<and> s_cont m_full' = Inl (prefix @ k))"
            by blast

          hence Absorbed' :
            "\<And> k m_full.
                   s_cont m_full = Inl (body # k) \<Longrightarrow>
                   payload m_full = payload m \<Longrightarrow> (\<exists>m_full'. sem_exec_c_p gs m_full i m_full' \<and> payload m_full' = m'x \<and> s_cont m_full' = Inl (prefix @ k))"
            by blast
  
          obtain m2' ::"('a, 'b) state"  where M2_exec :
            "(sem_exec_c_p gs m2 i m2' \<and> payload m2' = m'x \<and> s_cont m2' = Inl (prefix @ (([G Swhile'C [body]] @ c'))))"
            using Absorbed'[OF M2_cont'  M2_pay]
            by blast

          obtain malt' ::"('a, 'b) state"  where Malt_exec :
            "(sem_exec_c_p gs malt i malt' \<and> payload malt' = m'x \<and> s_cont malt' = Inl (prefix @ ((replicate n' body @ [G SwhileC' [G Sskip' []]]) @ c')))"
            using Absorbed' Malt_cont' Malt_pl
            by blast

          have "imm_safe gs malt'" sorry (* since malt is known to be safe *)

          obtain maltb' ::"('a, 'b) state"  where Maltb' :
            "(sem_exec_c_p gs maltb i maltb' \<and> payload maltb' = m'x \<and> s_cont maltb' = Inl (prefix @ []))"
            using Absorbed'[OF Maltb_cont Maltb_pl] Maltb_cont
            by blast

          obtain j where 
            Jleq : "j \<le> Suc i"
            and Imax' : "\<not> (\<exists>prefix st'.
                          \<forall>k m_full.
                             s_cont m_full = Inl (body # k) \<longrightarrow>
                             payload m_full = payload m \<longrightarrow>
                             (\<exists>m_full'.
                                 sem_exec_c_p gs m_full j m_full' \<and>
                                 payload m_full' = st' \<and>
                                 s_cont m_full' = Inl (prefix @ k)))"
            using Imax unfolding absorbs_def
            by auto

          show "imm_safe gs m'"
          proof(cases "j = Suc i")
            case False' : False

            hence Jleq' : "j \<le> i" using Jleq by auto

            have Uhoh : "(\<exists>prefix st'.
                          \<forall>k m_full.
                             s_cont m_full = Inl (body # k) \<longrightarrow>
                             payload m_full = payload m \<longrightarrow>
                             (\<exists>m_full'.
                                 sem_exec_c_p gs m_full j m_full' \<and>
                                 payload m_full' = st' \<and>
                                 s_cont m_full' = Inl (prefix @ k)))"
              using Iabs Jleq' unfolding absorbs_def
              by blast

            have False
              using Imax' Uhoh by blast

            then show ?thesis by auto
          next
            case True' : True
(* case split on whether prefix is [].
if it is nil, "apply induction on the case n-j" (i.e., spill over into next iteration *)

(* if prefix is non-nil, we need some fact about how the resulting continuation
will be the same between malt' and m2'

*)

            show "imm_safe gs m'"
            proof(cases prefix)
              case Nil
              then show ?thesis (* do an inductive thingy, n - j < n *) sorry
            next
              case (Cons preh pret)

              obtain mfin1 mfin1p kfin1 where "sem_exec_c_p gs m2' 1 mfin1 \<and> payload mfin1 = mfin1p \<and> s_cont mfin1 = kfin1" sorry

(* we know we are safe here (malt') *)

              obtain mfin2 mfin2p kfin2 where "sem_exec_c_p gs malt' 1 mfin2 \<and> payload mfin2 = mfin2p \<and> s_cont mfin2 = kfin2"
                sorry

              show "imm_safe gs m'"
                using HTE[OF Htrue] 

(* idea: we are looking at some kind of function f where 
f ((ph#pt) @ ((replicate n' body @ [G SwhileC' [G Sskip' []]]) @ c'))) =
f ((ph#pt) @ (([G Swhile'C [body]] @ c')))
*)

(* executing preh should be imm. safe - regardless of whether this happens in maltb' or malt' *)
(* we need to be able to use the fact that lack of suffix implies escape happens. but unlike appel's system,
our continuations might be too free-form to make this work.

i don't think this is quite it... it's that we cant' say much about the resulting continuation after escaping
whereas in appel's system blocks seem to help.

we cannot allow arbitrary modification of k.
prepending seems ok. postpending seems probably ok.

another view: dropping from beginning seems fine. adding on end seems fine.

another view: something about dependence between data and control (? not making
structural decisions about shape of control using data? vice versa?)
*)
              then show ?thesis sorry
            qed


(*
"\<And>prefix a aa b.
       (\<And> k m_full.
          s_cont m_full = Inl (body # k) \<Longrightarrow>
          payload m_full = payload m \<Longrightarrow>
          (\<exists>m_full'.
              sem_exec_c_p gs m_full j m_full' \<and>
              payload m_full' = (a, aa, b) \<and> s_cont m_full' = Inl (prefix @ k))) \<Longrightarrow> False"
*)

(* idea: 2 possibilities at this point
- stepping into prefix results in an empty continuation \<Rightarrow> we are done
- stepping into the prefix results in "escape" beyond the loop.
however, can we cheat at this point? use information from the continuation list to do
different things in different cases in a way that is bad?
*)

(* we still have n-i steps to go ... we need to know something about the behavior of the prefix. *)

(* one idea: prefix cannot choose whether to fail based on data (or shape) of continuation *)
(* another idea: just based on data of continuation *)

(* prefix should be safe for any state that was produced from running body starting at P1 *)
(* {-?-} prefix {-P1-} *)

            have "|gs| {-(\<lambda> st . st = m'x)-} prefix {-P1-}"
            proof
              fix cx

              assume G : "|gs| {P1} cx"
              show "|gs| {\<lambda>st. st = m'x} prefix @ cx"
              proof
                fix mp :: "('a, 'b) state"
                assume Hmp : "(payload mp) = m'x"
                assume Hmpc : "s_cont mp = Inl (prefix @ cx)"

                have "|gs| {P1} [body] @ cx" using HTE[OF Htrue G] by auto

                show "safe gs mp" 
                proof
                  fix mp'

                  assume "sem_exec_p gs mp mp'"
                  show "imm_safe gs mp'"


            then show ?thesis 
          qed

          have False using Imax Iabs unfolding absorbs_def

(*
exists Suc i where
forall prefix st'
exists k, m_full where
s_cont m_full \<noteq> Inl (body # k) \<and>
payload m_full 
*)

(* idea: we know prefix must be something that throws away the continuation. the appel paper does a specific case analysis on "non-local"
control flow at this point. perhaps we need to do the same? this would require a "closed world" of non-local control flow when we instantiate
this theorem, which isn't unreasonable. *)
          then show ?thesis using  Imax unfolding absorbs_def
        qed
      qed
    qed
  qed
qed


(*
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
  assume Guard : " |gs| {C False} c'"

  show "|gs| {P1} ([G Swhile'C [body]]) @ c'"
  proof
    fix m :: "('a, 'b) state"
    assume Mp : "P1 (payload m)"
    assume Mc : "s_cont m = Inl (([G Swhile'C [body]]) @ c')"
    show "safe gs m"
    proof
      fix m' :: "('a, 'b) state"

      assume Exec : "sem_exec_p gs m m'"

      obtain cnt where Exec' : "sem_exec_c_p gs m cnt m'"
        using exec_p_imp_exec_c_p[OF Exec] by auto

      have "|gs| {- P1  -} replicate cnt body @ [(G Swhile'C [body])] {- (\<lambda> st . False ) -}"

      then show "imm_safe gs m'" using Guard Mp Mc
      proof(induction arbitrary: c' rule: sem_exec_c_p.induct)
        case (Excp_0 m0)
        then show ?case unfolding imm_safe_def sorry
      next
        case (Excp_Suc m1 m2 n m3)
        then show ?case 
      qed
*)
end