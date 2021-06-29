theory ImpCtl
  imports "../Gensyn" "../Gensyn_Descend" "../Mergeable/Mergeable" "../Mergeable/MergeableInstances"
          "../Lifting/LiftUtils" "../Lifting/LiftInstances"
          "../Lifting/AutoLift" "../Hoare/CPS_Hoare_Steps" "../Lifting/LangCompFull"
          "Utils"
          "./Seq"
begin

(* conditional/boolean expressions *)
datatype cond_syn' =
  Seqz
  | Sltz
  | Sgtz
  | Sskip_cond

type_synonym cond_state' = "bool * int"

definition cond_sem :: "cond_syn' \<Rightarrow> cond_state' \<Rightarrow> cond_state'" where
"cond_sem x s =
  (case s of (b, i) \<Rightarrow>
    (case x of
      Seqz \<Rightarrow> ((i = 0), i)
      | Sltz \<Rightarrow> ((i < 0), i)
      | Sgtz \<Rightarrow> ((i > 0), i)
      | Sskip_cond \<Rightarrow> s))"

(* Imp control
- IF
- WHILE
- SKIP
*)

datatype syn' =
  Sif
  | Sskip
  | Swhile
  | SwhileC

type_synonym 'x imp_state' = "'x gensyn list * bool"

type_synonym 'x state' = "'x gensyn list * bool * int"

(* TODO: finish while case *)
(* TODO: error? *)
(*
while ==
- push condition
- push while [body]
- push while [cond, body]
*)

(* while [body] \<Longrightarrow> check condition *)

definition imp_ctl_sem :: "syn' \<Rightarrow> 'x imp_state' \<Rightarrow> 'x imp_state'" where
"imp_ctl_sem x st =
  (case st of
    ([], b) \<Rightarrow> ([], b)
    | ((G z l)#t, b) \<Rightarrow>
      ((case x of
        Sskip \<Rightarrow> t
        | Sif \<Rightarrow>
        (case l of
          [body] \<Rightarrow> (if b then body#t else t)
          | [cond, body] \<Rightarrow> cond# ((G z [body])#t)
          | _ \<Rightarrow> [] \<comment>\<open> error \<close>)
        | Swhile \<Rightarrow>
        (case l of
         [cond, body] \<Rightarrow> cond # (G z [cond, cond, body]) # t
         | [cond, _, body] \<Rightarrow> (if b then body # (G z [cond, body]) # t else t)
         | _ \<Rightarrow> [] \<comment> \<open> error \<close>)
        | SwhileC \<Rightarrow>
        (case l of [body] \<Rightarrow> (if b then body # (G z [body]) # t else t)
         | _ \<Rightarrow> []))
      , b))"

(*
while (full - boolean  on stack)
if b then body # while # t else t

*)

datatype syn = 
  Simp syn'
  | Scond cond_syn'
  | Seq "Seq.syn"

type_synonym ('s, 'x) state = 
  "('s, (bool md_triv option md_prio * int md_triv option md_prio * 'x)) control"

type_synonym ('s) cstate = 
  "('s, unit option) state"


definition imp_trans :: "ImpCtl.syn \<Rightarrow> ImpCtl.syn'" where
"imp_trans s =
  (case s of
    Simp s' \<Rightarrow> s'
    | _ \<Rightarrow> Sskip)"

definition cond_trans :: "syn \<Rightarrow> cond_syn'" where
"cond_trans s =
  (case s of
    Scond x \<Rightarrow> x
    | _ \<Rightarrow> Sskip_cond)"

definition seq_trans :: "syn \<Rightarrow> Seq.syn" where
"seq_trans s =
  (case s of
    Seq x \<Rightarrow> x
    | _ \<Rightarrow> Seq.Sskip)"

definition imp_prio :: "(syn' \<Rightarrow> nat)" where
"imp_prio x =
(case x of
    Sskip \<Rightarrow> 0
    | _ \<Rightarrow> 2)"


definition imp_sem_lifting_gen :: "(ImpCtl.syn', 'x imp_state', 
                                   ('x, _ ) state) lifting" where
"imp_sem_lifting_gen = 
 (schem_lift (SP NA NB)
             (SP (SPRC imp_prio (SO NA)) (SP NX (SP (SPRK (SO NB)) NX))))"


definition imp_sem_l_gen :: "('s \<Rightarrow> ImpCtl.syn') \<Rightarrow> 's \<Rightarrow> ('x, 'z :: Mergeableb) state \<Rightarrow> ('x, 'z) state" where
"imp_sem_l_gen lfts =
  lift_map_s lfts
    imp_sem_lifting_gen
  imp_ctl_sem"

definition seq_sem_l' :: "syn \<Rightarrow> ('x, 'z :: Mergeableb) state \<Rightarrow> ('x, 'z) state" where
"seq_sem_l' = seq_sem_l_gen seq_trans"

definition sems :: "(syn \<Rightarrow> ('x, 'z :: Mergeableb) state \<Rightarrow> ('x, 'z :: Mergeableb) state) list" where
"sems = [seq_sem_l_gen seq_trans, imp_sem_l_gen imp_trans]"

definition sem_final :: "(syn, 'x, bool md_triv option md_prio * 
                                           int md_triv option md_prio
                                    * unit option) sem" where
"sem_final = \<lparr> s_sem = (pcomps' sems) \<rparr>"

definition prog where
"prog = (G (Seq Sseq) [(G (Seq Sseq) []), 
                        (G (Simp Sif) [(G (Seq Sseq) []), (G (Seq Sseq) [])])])"

definition get_cond :: 
"bool md_triv option md_prio * 
  int md_triv option md_prio * 
  (_ :: Pordb) \<Rightarrow> bool option" where
"get_cond st = 
  (case st of
    (b, _, _) \<Rightarrow> 
    (case b of
      (mdp _ (Some (mdt b'))) \<Rightarrow> Some b'
      | _ \<Rightarrow> None))"



(*
do we need to take into account "separation" between imp and cond?
we probably need to model cond running for possibly multiple steps.
*)
(* can we eliminate P2? *)
(* probably not, unless we require P2 to be an expression language.
   besides this should be fine. *)
(* we need to enforce that the initial state is valid.
that is, that it falls into the valid set given by the imp lifting. *)
lemma HIf_gen :
  assumes H0 : "gs = \<lparr> s_sem = pcomps' fs \<rparr>"
  (*assumes H1 : "seq_sem_l_gen lfts \<in> set fs" *)
  assumes HF : "f = imp_sem_l_gen lfts"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hnemp : "g \<in> set fs"
  assumes Hdom : "(f \<downharpoonleft> (set fs) Sif')"
  assumes Hsyn : "lfts Sif' = Sif"
  (* TODO: generalize. these should be expressed using valid-sets *)
  assumes P1_valid : "\<And> st.  P1 st \<Longrightarrow> get_cond st \<noteq> None"
  assumes P2_valid : "\<And> st . P2 st \<Longrightarrow> get_cond st \<noteq> None"

  assumes Hcond : "|gs| {- P1, np1 -} [cond] {- P2, np2 -}"
  assumes Htrue : "|gs| {- (\<lambda> st . P2 st \<and> get_cond st = Some True), np2 -} [body]
                        {- P3, np3 -}"
  assumes Hfalse : "|gs| {- (\<lambda> st . P2 st \<and> get_cond st = Some False), np2 -} [] {-P3, np3-}" 
(* TODO: as with Seq, we could tighten this to 1+ *)
  shows "|gs| {- P1, np1 -} [G Sif' [cond, body]] {- P3, np3 -}"
proof
  fix c'

  assume Guard : "|gs| {P3, np3} c'"

  have Gtrue : "|gs| {(\<lambda>st . P2 st \<and> get_cond st = Some True), np2} ([body] @ c')"
    using HTE[OF Htrue Guard] by auto

  have Gfalse : "|gs| {(\<lambda>st . P2 st \<and> get_cond st = Some False), np2}  ([] @ c')"
    using HTE[OF Hfalse Guard] by auto

  show "|gs| {P1, np1} ([G Sif' [cond, body]] @ c')"
  proof
    fix m :: "('a, 'b) state"

    assume M : "P1 (payload m)"
    assume CM : "s_cont m = Inl ([G Sif' [cond, body]] @ c')"

    show "(safe_for gs m np1)"
    proof(cases "(sem_step gs m)")
      case (Inr bad)

      then have False using CM H0
        by(auto simp add: sem_step_def)

      then show ?thesis by auto
    next
      case (Inl m')

      have F_eq : "sem_step \<lparr> s_sem = f \<rparr> m = Inl m'"
        using sym[OF dominant_pcomps'[OF Hpres Hnemp Hdom]] CM Inl H0
        by(simp add: sem_step_def)

      have CM' : "s_cont m' = Inl ([cond] @ ([ G Sif' [body]] @ c'))" 
        using CM Hsyn F_eq unfolding HF
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

      have Step_Inl : "sem_step_p gs m m'" using Inl unfolding sem_step_p_eq by simp

      (* next: step to the end of cond. *)

      have Sub : "|gs| {P2, np2} ([G Sif' [body]] @ c')"
      proof
        fix mp2 :: "('a, 'b) state"

        assume MP2 : "P2 (payload mp2)"

        assume Cont2 : "s_cont mp2 = Inl ([G Sif' [body]] @ c')"

        show "safe_for gs mp2 np2"
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

            have Mp2'_p2 : "P2 (payload mp2') "
              using Cont2 Hsyn H0 MP2 F_eq' P2_valid[OF MP2] Some' unfolding HF
              by(cases mp2; cases mp2'; 
                  auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
                  schem_lift_defs 
                  merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
                  get_cond_def
                  split: md_prio.splits md_triv.splits option.splits)

            have Inl_p : "sem_step_p gs mp2 mp2'"
              using Inl unfolding sem_step_p_eq by simp

            have Step_Inl : "sem_exec_c_p gs mp2 1 mp2'"
              using sem_exec_c_p.intros(2)[OF Inl_p Excp_0]
              by auto

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

              have Mp2'_safe : "safe_for gs mp2' np2"
                using guardedD[OF Gtrue Mp2'_p2_true Mp2'_cont] by auto

              have Thes' : "safe_for gs mp2 (1 + np2)" using safe_for_extend[OF Mp2'_safe Step_Inl]
                by auto

              show ?thesis using safe_for_weaken[OF Thes', of np2] by auto
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

              have Mp2'_safe : "safe_for gs mp2' np2"
                using guardedD[OF Gfalse Mp2'_p2_false Mp2'_cont] by auto

              have Thes' : "safe_for gs mp2 (1 + np2)" using safe_for_extend[OF Mp2'_safe Step_Inl]
                by auto

              show ?thesis using safe_for_weaken[OF Thes', of np2] by auto
            qed
          qed
        qed
      qed

      have Guard1 : "|gs| {P1, np1} [cond] @ [G Sif' [body]] @ c'"
        using HTE[OF Hcond Sub] by simp

      have Step' : "sem_exec_c_p gs m 1 m'"
        using sem_exec_c_p.intros(2)[OF Step_Inl sem_exec_c_p.intros(1)] by auto

      have Thes'' : "safe_for gs m' np1"
        using guardedD[OF Guard1 P1sm' CM']
        by auto

      have Thes'' : "safe_for gs m (1 + np1)"
        using safe_for_extend[OF Thes'' Step']
        by auto

      show "safe_for gs m np1"
        using safe_for_weaken[OF Thes'', of np1] by auto
    qed
  qed
qed


lemma rtranclp_induct_alt :
  assumes H : "rtranclp r a b" 
  assumes Ha : "P a" 
  assumes Hsteps : "(\<And> y z . rtranclp r a y \<Longrightarrow> rtranclp r y z \<Longrightarrow> P y \<Longrightarrow> P z)" 
  shows "P b" using assms
proof(induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step y z)

  have Py : "P y" using step.IH[OF step.prems(1) step.prems(2)]
    by auto

  have Rz : "rtranclp r y z" using step.hyps
    by(auto)

  show ?case using step.prems(2)[OF step.hyps(1) Rz Py] by auto
qed


lemma HWhileC_gen :
  assumes H0 : "gs = \<lparr> s_sem = pcomps' fs \<rparr>"
  (*assumes H1 : "seq_sem_l_gen lfts \<in> set fs" *)
  assumes HF : "f = imp_sem_l_gen lfts"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hnemp : "g \<in> set fs"
  assumes Hdom : "(f \<downharpoonleft> (set fs) SwhileC')"
  assumes Hsyn : "lfts SwhileC' = SwhileC"
  (* TODO: generalize. these should be expressed using valid-sets *)
  assumes PX_valid : "\<And> st.  PX st \<Longrightarrow> get_cond st \<noteq> None"
(* TODO: this next one is almost definitely going to have to be loosened *)
(* one idea: require nb1' be greater than nb2 (i.e. prepending loop body cannot cause a crash *)
(* also, we might need to tweak this to bring it in line with what our actual definition of HT
ends up being. *)
  assumes Htrue : "\<And> nb2 . \<exists> nb1' . |gs| {- PX, (nb1' + nb2) -} [body] {- PX, nb2 -}"
  assumes NLs : "nl1 \<le> nl2"
  shows "|gs| {- PX, nl1  -} [G SwhileC' [body]] {- (\<lambda> st . PX st \<and> get_cond st = Some False), nl2 -}"
proof
  fix c'

  assume Guard : "|gs| {\<lambda>st. PX st \<and> get_cond st = Some False, nl2} c'"

  show "|gs| {PX, nl1} [G SwhileC' [body]] @ c'" 
    using Guard NLs
  proof(induction nl2 arbitrary: nl1 c')
    case 0
    show ?case
    proof
      fix m :: "('a, 'b) state"
      assume Hm : " PX (payload m)"

      have Nl1_0 : "nl1 = 0" using 0 by auto

      assume Hcontm : "s_cont m = Inl ([G SwhileC' [body]] @ c')" 


      have Conc' : "sem_exec_c_p gs m 0 m \<and> s_cont m = Inl ((G SwhileC' [body]) # c')"
        using Hcontm Excp_0[of gs m] by auto

      show "safe_for gs m nl1" 
        using Conc'
        unfolding Nl1_0 safe_for_def
        by blast
    qed
  next
    case (Suc nl2')
    show ?case 
    proof
      fix m :: "('a, 'b) state"
      assume Hm : "PX (payload m)" 

      assume Hcontm : "s_cont m = Inl ([G SwhileC' [body]] @ c')" 
      show  "safe_for gs m nl1" 

      proof(cases "(sem_step gs m)")
        case (Inr bad)
  
        then have False using Hcontm H0
          by(auto simp add: sem_step_def)
  
        then show ?thesis by auto
      next
        case (Inl m')

        have F_eq : "sem_step \<lparr> s_sem = f \<rparr> m = Inl m'"
          using sym[OF dominant_pcomps'[OF Hpres Hnemp Hdom]] Hcontm Inl H0
          by(simp add: sem_step_def)
  
        have M_P1 : "PX (payload m)" using Hm Hcontm by auto
  
        have M'_valid : "\<And> p . fst (payload m) \<noteq> mdp p None" using PX_valid[OF M_P1]
          by(auto simp add: get_cond_def split:prod.splits)
  
        have Sm' : "payload m = payload m'"
          using Hcontm Hsyn F_eq M'_valid  unfolding HF
          by(cases m; cases m'; auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
             schem_lift_defs 
            merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
            split: md_prio.splits md_triv.splits option.splits)
  
        have M' : "PX (payload m')" using Sm' M_P1 by auto

        show "safe_for gs m nl1"
        proof(cases "get_cond (payload m)")
          case None
  
          then have False using PX_valid[OF M_P1]
            by(auto simp add: get_cond_def split: prod.splits md_prio.splits md_triv.splits option.splits)
          then show ?thesis by auto
  
        next
          case Some' : (Some cnd)

          have Helper : "|gs| {(\<lambda> st . PX st \<and> get_cond st = Some False), nl2'} c'"
          proof
            fix ml :: "('a, 'b) state"
            assume Hpay : "PX (payload ml) \<and> get_cond (payload ml) = Some False"

            assume Hcont : "s_cont ml = Inl c'"

            have Conc' : "safe_for gs ml (Suc nl2')"
              using guardedD[OF Suc.prems(1) Hpay Hcont]
              by auto

            show "safe_for gs ml nl2'"
              using safe_for_weaken[OF Conc', of nl2'] by auto
          qed

          show ?thesis
          proof(cases cnd)
            case True

            have M'_cont : "s_cont m' = Inl ([body, G SwhileC' [body]] @ c')"
                using Hsyn H0 M' F_eq True Some' Hcontm  unfolding HF
                by(cases m; auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
                  schem_lift_defs 
                  merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
                  get_cond_def
                  split: md_prio.splits md_triv.splits option.splits)

            have G1 : "|gs| {PX, nl2'} ([G SwhileC' [body]] @ c')"
              using Suc.IH[OF Helper] by auto

            hence G1' :  "|gs| {PX, (Suc nl2' - 1)} ([G SwhileC' [body]] @ c')"
              using Suc.IH[OF Helper] by auto

            obtain nb where NB : "|gs| {-PX, (nb + nl2')-} [body] {-PX, nl2'-}"
              using Htrue[of nl2'] by auto

            have Ggood : "|gs| {PX, (nb + nl2')} ([body] @ [G SwhileC' [body]] @ c')" 
              using HTE[OF NB G1] by auto

            have Almost :  "safe_for gs m' (nb + nl2')" using guardedD[OF Ggood M'] M'_cont
              by auto

            have Step : "sem_step_p gs m m'" using Inl
              unfolding sem_step_p_eq
              by auto
      
            have Step' : "sem_exec_c_p gs m 1 m'"
              using sem_exec_c_p.intros(2)[OF Step sem_exec_c_p.intros(1)] by auto

            have Conc' : "safe_for gs m (1 + nb + nl2')"
              using safe_for_extend[OF Almost Step'] by auto

            have Leq : "nl1 \<le> 1 + nb + nl2'" using Suc.prems by auto

            show "safe_for gs m nl1"
              using safe_for_weaken[OF Conc' Leq] by auto
          next

            case False

            have M'_cont : "s_cont m' = Inl (c')"
                using Hsyn H0 M' F_eq False Some' Hcontm  unfolding HF
                by(cases m; auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
                  schem_lift_defs 
                  merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
                  get_cond_def
                  split: md_prio.splits md_triv.splits option.splits)


            have M'_full' : "PX (payload m') \<and> get_cond (payload m') = Some False"
              using M' False Some' unfolding Suc.prems(1) Sm'
              by auto

            have Almost : "safe_for gs m' (Suc nl2')"
              using guardedD[OF Suc.prems(1) M'_full' M'_cont] by auto

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

end