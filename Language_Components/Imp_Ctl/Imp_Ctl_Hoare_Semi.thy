theory Imp_Ctl_Hoare_Semi
  imports Imp_Ctl "../../Hoare/Hoare"  "../../Hoare/Hoare_Indexed_Sound"
begin

(* Implementation of Hoare rules for WHILE and IF.
 * Provides an interesting example of using the step-count-indexed version of Hoare
 * logic to prove a theorem not easily provable without that abstraction
 * (this was what motivated the development of that abstraction).
 *)

(* This if rule looks a bit different from the traditional one;
 * this is mostly because evaluation of the condition (cond) may have
 * side effects. *)
lemma HIf :
  assumes H0 : "gs = pcomps fs"
  assumes HF : "f = imp_sem_l_gen lfts"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hnemp : "g \<in> set fs"
  assumes Hdom : "(f \<downharpoonleft> (set fs) Sif')"
  assumes Hsyn : "lfts Sif' = Sif"
  assumes P1_valid : "\<And> st.  P1 st \<Longrightarrow> get_cond st \<noteq> None"
  assumes P2_valid : "\<And> st . P2 st \<Longrightarrow> get_cond st \<noteq> None"

  assumes Hcond : "|gs| {- P1 -} [cond] {- P2 -}"
  assumes Htrue : "|gs| {- (\<lambda> st . P2 st \<and> get_cond st = Some True) -} [body]
                        {- P3 -}"
  assumes Hfalse : "|gs| {- (\<lambda> st . P2 st \<and> get_cond st = Some False) -} [] {-P3-}"
  shows "|gs| {- P1 -} [G Sif' [cond, body]] {- P3 -}"
proof
  fix c'
  assume Guard : "|gs| {P3} c'"

  have Gtrue : "|gs| {(\<lambda>st. P2 st \<and> get_cond st = Some True)} ([body] @ c')"
    using HTE[OF Htrue Guard] by auto

  have Gfalse : "|gs| {(\<lambda>st. P2 st \<and> get_cond st = Some False)} ([] @ c')"
    using HTE[OF Hfalse Guard] by auto

  show "|gs| {P1} ([G Sif' [cond, body]] @ c')"
  proof
    fix m :: "('a, 'b) state"

    assume M : "P1 (payload m)"
    assume CM : "cont m = Inl ([G Sif' [cond, body]] @ c')"

    show "(safe gs m)"
    proof(cases "(sem_step gs m)")
      case (Inr bad)

      then have False using CM H0
        by(auto simp add: sem_step_def)

      then show ?thesis by auto
    next
      case (Inl m')

      have F_eq : "sem_step f m = Inl m'"
        using sym[OF dominant_pcomps[OF Hpres Hnemp Hdom]] CM Inl H0
        by(simp add: sem_step_def)

      have CM' : "cont m' = Inl ([cond] @ ([ G Sif' [body]] @ c'))" 
        using CM Hsyn F_eq unfolding HF
        by(cases m; auto simp add: cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
           schem_lift_defs 
          merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def
          split: md_prio.splits md_triv.splits option.splits)

      have M'_valid : "\<And> p . fst (payload m) \<noteq> mdp p None" using P1_valid[OF M]
        by(auto simp add: get_cond_def split:prod.splits)

      have Sm' : "payload m = payload m'"
        using CM Hsyn F_eq M'_valid  unfolding HF
        by(cases m; auto simp add: cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
           schem_lift_defs 
          merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
          split: md_prio.splits md_triv.splits option.splits)

      hence P1sm' : "P1 (payload m')" using M unfolding Sm' by auto

      (* step to the end of cond. *)

      have Sub : "|gs| {P2} ([G Sif' [body]] @ c')"
      proof
        fix mp2 :: "('a, 'b) state"

        assume MP2 : "P2 (payload mp2)"

        assume Cont2 : "cont mp2 = Inl ([G Sif' [body]] @ c')"

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

            have F_eq' : "sem_step f mp2 = Inl mp2'"
              using sym[OF dominant_pcomps[OF Hpres Hnemp Hdom]] Cont2 Inl H0
              by(simp add: sem_step_def)

            have Mp2'_p2 : "P2 (payload mp2')"
              using Cont2 Hsyn H0 MP2 F_eq' P2_valid[OF MP2] Some' unfolding HF
              by(cases mp2; 
                  auto simp add: cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
                  schem_lift_defs 
                  merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
                  get_cond_def
                  split: md_prio.splits md_triv.splits option.splits)

            show ?thesis
            proof(cases cnd)
              case True
        
              have Mp2'_cond : "get_cond (payload mp2') = Some True" 
                using Cont2 Hsyn H0 MP2 F_eq' P2_valid[OF MP2] True Some' unfolding HF
                by(cases mp2; 
                    auto simp add: cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
                    schem_lift_defs 
                    merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
                    get_cond_def
                    split: md_prio.splits md_triv.splits option.splits)

              have Mp2'_p2_true :  "P2 (payload mp2') \<and> get_cond (payload mp2') = Some True"
                using Mp2'_p2 Mp2'_cond
                by auto

              have Mp2'_cont : "cont mp2' = Inl ([body] @ c')"
                using Cont2 Hsyn H0 MP2 F_eq' P2_valid[OF MP2] True Some' unfolding HF
                by(cases mp2; cases mp2'; 
                    auto simp add: cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
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
                by(cases mp2; 
                    auto simp add: cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
                    schem_lift_defs 
                    merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
                    get_cond_def
                    split: md_prio.splits md_triv.splits option.splits)

              have Mp2'_p2_false :  "P2 (payload mp2') \<and> get_cond (payload mp2') = Some False"
                using Mp2'_p2 Mp2'_cond
                by auto

              have Mp2'_cont : "cont mp2' = Inl ([] @ c')"
                using Cont2 Hsyn H0 MP2 F_eq' P2_valid[OF MP2] False Some' unfolding HF
                by(cases mp2; 
                    auto simp add: cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
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

      have Guard' : "|gs| {P1} ([cond] @ ([G Sif' [body]] @ c'))"
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

lemma HWhileC_idx :
  assumes H0 : "gs = pcomps fs"
  assumes HF : "f = imp_sem_l_gen lfts"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hnemp : "g \<in> set fs"
  assumes Hdom : "(f \<downharpoonleft> (set fs) SwhileC')"
  assumes Hsyn : "lfts SwhileC' = SwhileC"
  assumes PX_valid : "\<And> st.  PX st \<Longrightarrow> get_cond st \<noteq> None"
  assumes Htrue : "HT'' gs PX [body] PX"
(*  assumes NLs : "nl1 \<le> nl2" *)
  shows "HT'' gs PX ([G SwhileC' [body]]) (\<lambda> st . PX st \<and> get_cond st = Some False)"
proof(rule HT''I)
  fix npre c'

  assume Guard : "(\<And>npost. |#gs#| {#(\<lambda>st. PX st \<and> get_cond st = Some False), npost#} c')"

  show "|#gs#| {#PX, npre#} ([G SwhileC' [body]] @ c')" 
    using Guard
  proof(induction npre arbitrary: c')
    case 0
    show ?case sorry
(*
    proof
      fix m :: "('a, 'b) state"
      assume Hm : " PX (payload m)"

      have Nl1_0 : "nl1 = 0" using 0 by auto

      assume Hcontm : "cont m = Inl ([G SwhileC' [body]] @ c')" 


      have Conc' : "sem_exec_c_p gs m 0 m \<and> cont m = Inl ((G SwhileC' [body]) # c')"
        using Hcontm Excp_0[of gs m] by auto

      show "safe_for gs m nl1" 
        using Conc'
        unfolding Nl1_0 safe_for_def
        by blast
    qed
*)
  next
    case (Suc nl1')
    show ?case 
    proof
      fix m :: "('a, 'b) state"
      assume Hm : "PX (payload m)" 

      assume Hcontm : "cont m = Inl ([G SwhileC' [body]] @ c')" 
      show  "safe_for gs m (Suc nl1')" 

      proof(cases "(sem_step gs m)")
        case (Inr bad)
  
        then have False using Hcontm H0
          by(auto simp add: sem_step_def)
  
        then show ?thesis by auto
      next
        case (Inl m')

        have F_eq : "sem_step f m = Inl m'"
          using sym[OF dominant_pcomps[OF Hpres Hnemp Hdom]] Hcontm Inl H0
          by(simp add: sem_step_def)
  
        have M_P1 : "PX (payload m)" using Hm Hcontm by auto
  
        have M'_valid : "\<And> p . fst (payload m) \<noteq> mdp p None" using PX_valid[OF M_P1]
          by(auto simp add: get_cond_def split:prod.splits)
  
        have Sm' : "payload m = payload m'"
          using Hcontm Hsyn F_eq M'_valid  unfolding HF
          by(cases m; auto simp add: cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
             schem_lift_defs 
            merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
            split: md_prio.splits md_triv.splits option.splits)
  
        have M' : "PX (payload m')" using Sm' M_P1 by auto

        show "safe_for gs m (Suc nl1')"
        proof(cases "get_cond (payload m)")
          case None
  
          then have False using PX_valid[OF M_P1]
            by(auto simp add: get_cond_def split: prod.splits md_prio.splits md_triv.splits option.splits)
          then show ?thesis by auto
  
        next
          case Some' : (Some cnd)

          have Helper : "(\<And>npost. |#gs#| {#(\<lambda>st. PX st \<and> get_cond st = Some False), npost#} c')"
          proof
            fix npost
            fix ml :: "('a, 'b) state"
            assume Hpay : "PX (payload ml) \<and> get_cond (payload ml) = Some False"

            assume Hcont : "cont ml = Inl c'"

            show "safe_for gs ml npost"
              using guardediD[OF Suc.prems(1) Hpay Hcont]
              by auto
          qed

          show ?thesis
          proof(cases cnd)
            case True

            have M'_cont : "cont m' = Inl ([body, G SwhileC' [body]] @ c')"
                using Hsyn H0 M' F_eq True Some' Hcontm  unfolding HF
                by(cases m; auto simp add: cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
                  schem_lift_defs 
                  merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
                  get_cond_def
                  split: md_prio.splits md_triv.splits option.splits)

            have G1 : "|#gs#| {#PX, nl1'#} ([G SwhileC' [body]] @ c')"
              using Suc.IH[OF Helper] by auto

            hence G1' :  "|#gs#| {#PX, (Suc nl1' - 1)#} ([G SwhileC' [body]] @ c')"
              using Suc.IH[OF Helper] by auto

            have Ggood : "|#gs#| {#PX, (nb + nl2')#} ([body] @ [G SwhileC' [body]] @ c')" 
              using HT''D[OF Htrue]

(*
            have G2 : "|gs| {-PX-} [body] {-PX-}"
              using Htrue by auto

            have Ggood : "|#gs#| {#PX, (nb + nl2')#} ([body] @ [G SwhileC' [body]] @ c')" 
              using HTE[OF G2] by auto

            have Almost :  "safe_for gs m' (nb + nl2')" using guardediD[OF Ggood M'] M'_cont
              by auto

            have Step : "sem_step_p gs m m'" using Inl
              unfolding sem_step_p_eq
              by auto
      
            have Step' : "sem_exec_c_p gs m 1 m'"
              using sem_exec_c_p.intros(2)[OF Step sem_exec_c_p.intros(1)] by auto

            have Conc' : "safe_for gs m (1 + nb + nl2')"
              using safe_for_extend[OF Almost Step'] by auto

            have Leq : "nl1 \<le> 1 + nb + nl2'" using Suc.prems by auto
*)
            show "safe_for gs m (Suc nl1')"
              using safe_for_weaken[OF Conc' Leq] by auto
          next

            case False

            have M'_cont : "cont m' = Inl (c')"
                using Hsyn H0 M' F_eq False Some' Hcontm  unfolding HF
                by(cases m; auto simp add: cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
                  schem_lift_defs 
                  merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
                  get_cond_def
                  split: md_prio.splits md_triv.splits option.splits)

            have M'_full' : "PX (payload m') \<and> get_cond (payload m') = Some False"
              using M' False Some' unfolding Suc.prems(1) Sm'
              by auto

            have Almost : "safe_for gs m' (Suc nl2')"
              using guardediD[OF Suc.prems(1) M'_full' M'_cont] by auto

            have Step : "sem_step_p gs m m'" using Inl
              unfolding sem_step_p_eq
              by auto

            have Step' : "sem_exec_c_p gs m 1 m'"
              using sem_exec_c_p.intros(2)[OF Step sem_exec_c_p.intros(1)] by auto

            have Conc' : "safe_for gs m (1 + Suc (nl2'))"
              using safe_for_extend[OF Almost Step'] by auto

            have Leq : "nl1 \<le> 1 + Suc nl2'" using Suc.prems by auto

            show "safe_for gs m nl1"
              using safe_for_weaken[OF Conc' Leq] by auto
          qed
        qed
      qed
    qed
  qed
qed

(* Using the soundness of our indexed Hoare triples, we can prove this rule in the normal
 * Hoare abstraction.
 * Note that because we could not prove completeness for the indexed triples,
 * we still require an assumption on the body that talks about indices.
 *)
lemma HWhileC_idx :
  assumes H0 : "gs = pcomps fs"
  assumes HF : "f = imp_sem_l_gen lfts"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hnemp : "g \<in> set fs"
  assumes Hdom : "(f \<downharpoonleft> (set fs) SwhileC')"
  assumes Hsyn : "lfts SwhileC' = SwhileC"
  assumes PX_valid : "\<And> st.  PX st \<Longrightarrow> get_cond st \<noteq> None"
  assumes Htrue : "|gs| {- PX-} [body] {- PX-}"
  assumes NLs : "nl1 \<le> nl2"
  shows "|gs| {-PX-} [G SwhileC' [body]] {- (\<lambda> st . PX st \<and> get_cond st = Some False)-}"
proof(rule HT'_imp_HT; rule HT'I)
  fix npre

  have Htrue' : "\<And> nb2 . \<exists> nb1' . |#gs#| {#- PX, (nb1' + nb2) -#} [body] {#- PX, nb2 -#}"

  show "\<exists>npost. |#gs#| {#-PX, npre-#} [G SwhileC' [body]] {#-(\<lambda>st. PX st \<and> get_cond st = Some False), npost-#}"


end