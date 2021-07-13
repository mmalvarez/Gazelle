theory Imp_Ctl
imports "../../Syntax/Gensyn" "../../Syntax/Gensyn_Descend" "../../Mergeable/Mergeable"
        "../../Mergeable/Mergeable_Instances"
        "../../Lifter/Lifter" "../../Lifter/Lifter_Instances"
        "../../Lifter/Auto_Lifter" "../../Lifter/Auto_Lifter_Proofs" 
        "../../Semantics/Semantics" 
        "../Utils"
begin

(*
 * Implementation of standard imperative-language control structures (If and While).
 * These are based off the idealized language IMP (see e.g. _Software Foundations_ vol. 1,, "Imp")
 * and lack constructs such as break and continue. However, the framework is flexible enough
 * to permit description of such constructs and even write Hoare rules for them
 * (for an example of how this might work, see Appel and Blazy,
 * "Separation Logic for Small-Step Cminor")
 *)

(* conditional/boolean expressions *)
(* these could be separated out into yet another file (TODO) *)
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

datatype syn' =
  Sif
  | Sskip
  | Swhile
  | SwhileC

type_synonym 'x imp_state' = "'x gensyn list * bool"

type_synonym 'x state' = "'x gensyn list * bool * int"

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

(* TODO: correctness theorem would be cleaner if we had a way to say that
   boolean expressions can't affect control flow (also in terms of domination?)
*)

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

  assumes Hcond : "|gs| {- P1 -} [cond] {- P2 -}"
  assumes Htrue : "|gs| {- (\<lambda> st . P2 st \<and> get_cond st = Some True) -} [body]
                        {- P3 -}"
  assumes Hfalse : "|gs| {- (\<lambda> st . P2 st \<and> get_cond st = Some False) -} [] {-P3-}"
  shows "|gs| {- P1 -} [G Sif' [cond, body]] {- P3 -}"
proof
  fix c'
  assume Guard : "|gs| {P3} c'"

  
(* need to think about how we are structuring states. *)
(* where will the data of interest be *)
  have Gtrue : "|gs| {\<lambda>st. P2 st \<and> get_cond st = Some True} [body] @ c'"
    using HTE[OF Htrue Guard] by auto

  have Gfalse : "|gs| {\<lambda>st. P2 st \<and> get_cond st = Some False} [] @ c'"
    using HTE[OF Hfalse Guard] by auto

  show "|gs| {P1} [G Sif' [cond, body]] @ c'"
  proof
    fix m :: "('a, 'b) state"

    assume M : "P1 (payload m)"
    assume CM : "s_cont m = Inl ([G Sif' [cond, body]] @ c')"

    show "(safe gs m)"
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

(* ok, if we were to define a step-counting version? *)

(*
another concept.

- start with while cond do body
- will not crash in cond
- will not crash in body

*)
(*
lemma HWhile_gen_ind :
  assumes H0 : "gs = \<lparr> s_sem = pcomps' fs \<rparr>"
  assumes HF : "f = imp_sem_l_gen lfts"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hnemp : "g \<in> set fs"
  assumes Hdom : "(f \<downharpoonleft> (set fs) Swhile')"
  assumes Hsyn : "lfts Swhile' = Swhile"
  (* TODO: generalize. these should be expressed using valid-sets *)
  assumes P1_valid : "\<And> st.  P1 st \<Longrightarrow> get_cond st \<noteq> None"

  assumes Hcond : "|gs| {- P1 -} [cond] {- P1 -}"
  assumes Htrue : "|gs| {- (\<lambda> st . P1 st \<and> get_cond st = Some True) -} [body]
                        {- P1 -}"

  assumes Hexec : 

  shows "|gs| {- P1 -} [G Swhile' [cond, body]] {- (\<lambda> st . P1 st \<and> get_cond st = Some False) -}"
*)

(*
lemma HWhile_gen' :
  assumes H0 : "gs = \<lparr> s_sem = pcomps' fs \<rparr>"
  (*assumes H1 : "seq_sem_l_gen lfts \<in> set fs" *)
  assumes HF : "f = imp_sem_l_gen lfts"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hnemp : "g \<in> set fs"
  assumes Hdom : "(f \<downharpoonleft> (set fs) Swhile')"
  assumes Hsyn : "lfts Swhile' = Swhile"
  (* TODO: generalize. these should be expressed using valid-sets *)
  assumes P1_valid : "\<And> st.  P1 st \<Longrightarrow> get_cond st \<noteq> None"

  assumes Hcond : "|gs| {- P1 -} [cond] {- P2 -}"
  assumes Htrue : "|gs| {- (\<lambda> st . P2 st \<and> get_cond st = Some True) -} [body]
                        {- P1 -}"
  assumes Hfalse : "|gs| {- (\<lambda> st . P2 st \<and> get_cond st = Some False) -} []
                        {- P1 -}" 

  shows "|gs| {- \<lambda> st . P1 st -} (concat (replicate n [cond, body]) @ (G Swhile' [cond, body])) {- (\<lambda> st . P1 st \<and> get_cond st = Some False) -}"
proof(induction n)
case 0
  then show ?case
  proof
    fix c'

    assume Guard : "|gs| {\<lambda>st. P1 st \<and> get_cond st = Some False} c'"

    then show "|gs| {\<lambda>st. P1 st \<and> get_cond st = Some False} replicate 0 (G Swhile' [cond, body]) @ c'"
      unfolding replicate.simps append.simps by auto
  qed
next
  case (Suc n)
  show ?case
  proof
    fix c'
    assume Guard : "|gs| {\<lambda>st. P1 st \<and> get_cond st = Some False} c'"

    show "|gs| {\<lambda>st. P1 st \<and> get_cond st = Some False} replicate (Suc n) (G Swhile' [cond, body]) @ c'"
      unfolding replicate.simps
    proof
      fix m :: "('a, 'b) state"
      assume HM_1 : "P1 (payload m) \<and> get_cond (payload m) = Some False"
      assume HM_Cont : "s_cont m = Inl ((G Swhile' [cond, body] # replicate n (G Swhile' [cond, body])) @ c')"

      show "safe gs m"
      proof(cases "(sem_step gs m)")
        case (Inr bad)
  
        then have False using HM_1 HM_Cont
          by(auto simp add: sem_step_def)
  
        then show ?thesis by auto
      next
        case (Inl m')
  
        have F_eq : "sem_step \<lparr> s_sem = f \<rparr> m = Inl m'"
          using sym[OF dominant_pcomps'[OF Hpres Hnemp Hdom]] HM_1 Inl H0 HM_Cont
          by(simp add: sem_step_def)
  
        have HM' : "s_cont m' = Inl ([cond] @ ( G Swhile' [cond, cond, body]  # replicate n (G Swhile' [cond, body])) @ c')" 
          using HM_1 HM_Cont Hsyn F_eq unfolding HF
          by(cases m; cases m'; auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
             schem_lift_defs 
            merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def
            split: md_prio.splits md_triv.splits option.splits)

        have P1_M : "P1 (payload m)" using HM_1 by auto

        (* this will need to be shown using valid-sets. *)
        have M'_valid : "\<And> p . fst (payload m) \<noteq> mdp p None" using P1_valid[OF P1_M]
          by(auto simp add: get_cond_def split:prod.splits)
  
        have Sm' : "payload m = payload m'"
          using HM_1 HM' HM_Cont Hsyn F_eq M'_valid  unfolding HF
          by(cases m; cases m'; auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
             schem_lift_defs 
            merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
            split: md_prio.splits md_triv.splits option.splits)
  
        hence P1sm' : "P1 (payload m')" using P1_M unfolding Sm' by auto

        show ?thesis using Suc.IH

qed
*)

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

(*
lemma rtranclp_induct_alt_stronger :
  "rtranclp r a b \<Longrightarrow> P a \<Longrightarrow>
   (\<And> y z . rtranclp r a y \<Longrightarrow> rtranclp r y z \<Longrightarrow> P y \<Longrightarrow> P z) \<Longrightarrow> P b"
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
*)

(* the issue here is that we don't really have any way of describing what might happen after
executing a prefix before the loop, since that prefix might do all kinds of crazy stuff
to the continuation

*)





definition fuel_bound :: "('syn, 'mstate) semc \<Rightarrow> ('syn gensyn list) \<Rightarrow> nat \<Rightarrow> bool" where
"fuel_bound gs cont n =
  (\<forall> st n' st' . s_cont st = Inl cont \<longrightarrow> 
     sem_exec_c_p gs st n' st' \<longrightarrow>
     s_cont st' = Inl [] \<longrightarrow>
     n' \<le> n)"

lemma fuel_boundI :
  assumes "\<And> st n' st' . s_cont st = Inl cont \<Longrightarrow>
     sem_exec_c_p gs st n' st' \<Longrightarrow>
     s_cont st' = Inl [] \<Longrightarrow>
     n' \<le> n"
  shows "fuel_bound gs cont n" using assms
  unfolding fuel_bound_def by blast

lemma fuel_boundD :
  assumes H : "fuel_bound gs cont n"
  assumes H1 : "s_cont st = Inl cont"
  assumes H2 : "sem_exec_c_p gs st n' st'"
  assumes H3 : "s_cont st' = Inl []"
  shows "n' \<le> n" using assms
  unfolding fuel_bound_def by blast

(* TODO: I think finiteness is necessary, but there is probably
a way to avoid this requirement if we introduce ghost variables or similar
(the reason it arises is that we need to pick a single fuel bound
for the entire state space (of terminating executions), but this is
possible only if the state is finite (?)
*)

lemma HWhileC_gen :
  assumes H0 : "gs = \<lparr> s_sem = pcomps' fs \<rparr>"
  (*assumes H1 : "seq_sem_l_gen lfts \<in> set fs" *)
  assumes HF : "f = imp_sem_l_gen lfts"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hnemp : "g \<in> set fs"
  assumes Hdom : "(f \<downharpoonleft> (set fs) SwhileC')"
  assumes Hsyn : "lfts Swhile' = SwhileC"
  (* TODO: generalize. these should be expressed using valid-sets *)
  assumes PX_valid : "\<And> n st.  PX n st \<Longrightarrow> get_cond st \<noteq> None"
  assumes Htrue : "\<And> n .  |gs| {-(\<lambda> st . PX n st)-} [body] {-(\<lambda> st . PX (n - 1) st)-}"
  assumes PX_P1 : "\<And> n st . PX n st \<Longrightarrow> P1 st"
  assumes PX_P1' : "\<And> st . P1 st \<Longrightarrow> PX ni st"
  assumes Donefor : "\<And> stx c . PX 0 (payload stx) \<Longrightarrow> s_cont stx = Inl ([G SwhileC' [body]] @ c) \<Longrightarrow> safe gs stx"
  shows "|gs| {- PX (ni :: nat)  -} [G SwhileC' [body]] {- (\<lambda> st . (\<exists> n . n \<le> ni \<and> PX n st \<and> get_cond st = Some False) ) -}"
proof
  fix c'
  assume Guard : "|gs| {\<lambda>st. (\<exists> n . n \<le> ni \<and> PX n st \<and> get_cond st = Some False)} c'"

  show "|gs| {PX ni} [G SwhileC' [body]] @ c'" using Guard
  proof(induction ni arbitrary: c')
    case 0
    show ?case
    proof
      fix m :: "('a, 'b) state"
      assume P0 : "PX 0 (payload m)" 
      assume C : "s_cont m = Inl ([G SwhileC' [body]] @ c')" 
      show  "safe gs m" using Donefor[OF P0 C] by auto
    qed
  next
    case (Suc ni)
    show ?case
    proof
      fix m :: "('a, 'b) state"
      assume PX : "PX (Suc ni) (payload m)" 
      assume C : "s_cont m = Inl ([G SwhileC' [body]] @ c')" 
      show  "safe gs m" 

      proof(cases "(sem_step gs m)")
        case (Inr bad)
  
        then have False using C H0
          by(auto simp add: sem_step_def)
  
        then show ?thesis by auto
      next
        case (Inl m')
  
        have F_eq : "sem_step \<lparr> s_sem = f \<rparr> m = Inl m'"
          using sym[OF dominant_pcomps'[OF Hpres Hnemp Hdom]] C Inl H0
          by(simp add: sem_step_def)
  
        have M_P1 : "PX (Suc ni) (payload m)" using PX C by auto
  
        have M'_valid : "\<And> p . fst (payload m) \<noteq> mdp p None" using PX_valid[OF M_P1]
          by(auto simp add: get_cond_def split:prod.splits)
  
        have Sm' : "payload m = payload m'"
          using C Hsyn F_eq M'_valid  unfolding HF
          by(cases m; cases m'; auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
             schem_lift_defs 
            merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
            split: md_prio.splits md_triv.splits option.splits)
  
        have M' : "PX (Suc ni) (payload m')" using Sm' M_P1 by auto

        show "safe gs m"
        proof(cases "get_cond (payload m)")
          case None
  
          then have False using PX_valid[OF M_P1]
            by(auto simp add: get_cond_def split: prod.splits md_prio.splits md_triv.splits option.splits)
          then show ?thesis by auto
  
        next
          case Some' : (Some cnd)

          have Haa : "|gs| {\<lambda>st. \<exists>n\<le>ni. PX n st \<and> get_cond st = Some False} c'"
          proof
            fix ml :: "('a, 'b) state"
            assume Hpay : "\<exists>n\<le>ni . PX n (payload ml) \<and> get_cond (payload ml) = Some False"
            assume Hcont : "s_cont ml = Inl c'"

            obtain nnew where Nnew_leq  : "nnew \<le> ni" and Nnew_spec : "PX nnew (payload ml) \<and> get_cond (payload ml) = Some False"
              using Hpay by auto

            have Nnew_leq' : "nnew \<le> Suc ni" using Nnew_leq by auto

            have Hpay' : "\<exists>n\<le>Suc ni . PX n (payload ml) \<and> get_cond (payload ml) = Some False"
              using Nnew_leq' Nnew_spec by auto

            show "safe gs ml" using guardedD[OF Suc.prems Hpay' Hcont] Suc.prems
              by auto
          qed


          then show ?thesis 
          proof(cases cnd)
            case True

            have Mp2'_cont : "s_cont m' = Inl ([body, G SwhileC' [body]] @ c')" sorry

            have G1 : "|gs| {PX ni} [G SwhileC' [body]] @ c'"
              using Suc.IH[OF Haa] Suc.IH
              by auto

            hence G1' : "|gs| {PX (Suc ni - 1)} [G SwhileC' [body]] @ c'"
              by auto

            have Ggood : "|gs| {PX (Suc ni)} [body] @ [G SwhileC' [body]] @ c'"
              using HTE[OF Htrue G1'] Htrue by auto

            have Almost :  "safe gs m'" using guardedD[OF Ggood M'] Mp2'_cont
              by auto

            show "safe gs m" 
            proof
              fix mfin

              assume "sem_exec_p gs m mfin"
              then show "imm_safe gs mfin" unfolding sem_exec_p_def
              proof(cases rule: rtranclp.cases)
                case rtrancl_refl
                then have "sem_step_p gs mfin m'" using Inl unfolding sem_step_p_eq by auto
                then show ?thesis unfolding imm_safe_def by blast
              next
                case (rtrancl_into_rtrancl b)

                have Step : "sem_step_p gs m m'" using Inl unfolding sem_step_p_eq by auto
                have Steps : "sem_exec_p gs m' mfin" using rtranclp_bisect1[OF sem_step_determ rtrancl_into_rtrancl(1) Step rtrancl_into_rtrancl(2)] unfolding sem_exec_p_def
                  by auto
                show ?thesis using safeD[OF Almost Steps] by auto
              qed
            qed
          next
            case False

            have Mp2'_cont : "s_cont m' = Inl ( c')" sorry

            have Haa' : "|gs| {\<lambda>st. \<exists>n\<le>Suc ni. PX n st \<and> get_cond st = Some False} c'"
            proof
              fix ml :: "('a, 'b) state"
              assume Hpay : "\<exists>n\<le>Suc ni . PX n (payload ml) \<and> get_cond (payload ml) = Some False"
              assume Hcont : "s_cont ml = Inl c'"
  
  
              show "safe gs ml" using guardedD[OF Suc.prems Hpay Hcont] Suc.prems
                by auto
            qed

            have "
     PX (Suc ni) (CPS_Hoare.payload m') \<and>
     get_cond (CPS_Hoare.payload m') = Some False"
              using False M' Sm' Some'
              by(auto)

              hence NewHyp : "\<exists>n\<le>Suc ni.
     PX (n) (CPS_Hoare.payload m') \<and>
     get_cond (CPS_Hoare.payload m') = Some False"
                by auto

              have "safe gs m'" using guardedD[OF Haa' NewHyp Mp2'_cont] by auto

            show "safe gs m" sorry (* as in True case, just extend one step. *)
          qed
        qed
      qed
    qed
  qed
qed


lemma HWhileC_gen :
  fixes PX :: "nat \<Rightarrow> (bool md_triv option md_prio \<times>
  int md_triv option md_prio \<times> 'b :: Mergeableb) \<Rightarrow> bool"
  assumes H0 : "gs = \<lparr> s_sem = pcomps' fs \<rparr>"
  (*assumes H1 : "seq_sem_l_gen lfts \<in> set fs" *)
  assumes HF : "f = imp_sem_l_gen lfts"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hnemp : "g \<in> set fs"
  assumes Hdom : "(f \<downharpoonleft> (set fs) SwhileC')"
  assumes Hsyn : "lfts Swhile' = SwhileC"
  (* TODO: generalize. these should be expressed using valid-sets *)
  assumes PX_valid : "\<And> n st.  PX n st \<Longrightarrow> get_cond st \<noteq> None"
  (* problem is here. *)
  assumes Htrue : "\<And> f .  |gs| {-(\<lambda> st . PX (f st) st)-} [body] {-(\<lambda> st . PX (f st - 1) st)-}"
  assumes PX_P1 : "\<And> n st . PX n st \<Longrightarrow> P1 st"
  assumes PX_P1' : "\<And> st x . getn st \<le> x \<Longrightarrow> P1 st \<Longrightarrow> PX x st"
  assumes Donefor : "\<And> stx c . PX 0 (payload stx) \<Longrightarrow> s_cont stx = Inl ([G SwhileC' [body]] @ c) \<Longrightarrow> safe gs stx"
  shows "|gs| {- (\<lambda> st . PX (getn st) st)  -} [G SwhileC' [body]] {- (\<lambda> st . (\<exists> n . n \<le> getn st \<and> PX n st \<and> get_cond st = Some False) ) -}"
proof
  fix c'
  assume Guard : "|gs| {\<lambda>st. \<exists>n\<le>getn st. PX n st \<and> get_cond st = Some False} c'"

  show "|gs| {\<lambda>st. PX (getn st) st} [G SwhileC' [body]] @ c'"
  proof
    fix m :: "('a, 'b) state"
    assume HX : "PX (getn (payload m)) (payload m)"

    assume Hcont : "s_cont m = Inl ([G SwhileC' [body]] @ c')"

    have Cont' : "\<And> z . getn (payload m) \<le> z \<Longrightarrow> PX z (payload m) \<Longrightarrow> safe gs m"
    proof-
      fix z
      assume Hi1 : "getn (payload m) \<le> z" 
      assume Hi2 : "PX z (payload m)"
      show "safe gs m" using Hcont Hi1 Hi2 Guard
      proof(induction z arbitrary: c' m)
        case 0
        then show ?case using Donefor[OF _] by auto
      next
        case (Suc ni)
        show ?case
        proof(cases "(sem_step gs m)")
          case (Inr bad)
    
          then have False using Suc.prems H0
            by(auto simp add: sem_step_def)
    
          then show ?thesis by auto
        next
          case (Inl m2)
    
          have F_eq : "sem_step \<lparr> s_sem = f \<rparr> m = Inl m2"
            using sym[OF dominant_pcomps'[OF Hpres Hnemp Hdom]] Suc.prems Inl H0
            by(simp add: sem_step_def)
    
          have M_P1 : "PX (Suc ni) (payload m)" using Suc.prems by auto
    
          have M'_valid : "\<And> p . fst (payload m) \<noteq> mdp p None" using PX_valid[OF M_P1]
            by(auto simp add: get_cond_def split:prod.splits)
    
          have Sm' : "payload m = payload m2"
            using Suc.prems Hsyn F_eq M'_valid  unfolding HF
            by(cases m; cases m2; auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
               schem_lift_defs 
              merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
              split: md_prio.splits md_triv.splits option.splits)
    
          have M' : "PX (Suc ni) (payload m2)" using Sm' M_P1 by auto
  
          show "?thesis"
          proof(cases "get_cond (payload m)")
            case None
    
            then have False using PX_valid[OF M_P1]
              by(auto simp add: get_cond_def split: prod.splits md_prio.splits md_triv.splits option.splits)
            then show ?thesis by auto
    
          next
            case Some' : (Some cnd)
            then show ?thesis 
            proof(cases cnd)
              case True

              have Mp2'_cont : "s_cont m2 = Inl ([body, G SwhileC' [body]] @ c')" sorry


              show "safe gs m" using Suc.IH
              proof
                fix m'

                assume Exec : "sem_exec_p gs m m'"

                obtain nstep where Nstep : "sem_exec_c_p gs m nstep m'"
                  using exec_p_imp_exec_c_p[OF Exec] by blast


(*                show "imm_safe gs m'" *)

 

                have Haa : "|gs| {\<lambda>st. \<exists>n\<le> getn st. PX n st \<and> get_cond st = Some False} c'"
                proof
                  fix ml :: "('a, 'b) state"
                  assume Hpay : "\<exists>n\<le>getn (payload ml) . PX n (payload ml) \<and> get_cond (payload ml) = Some False"
                  assume Hcont : "s_cont ml = Inl c'"
    
                  obtain nnew where Nnew_leq  : "nnew \<le> getn (payload ml)" and Nnew_spec : "PX nnew (payload ml) \<and> get_cond (payload ml) = Some False"
                    using Hpay by auto
    
                  have Nnew_leq' : "nnew \<le> Suc (getn (payload ml))" using Nnew_leq by auto
    
                  have Hpay' : "\<exists>n\<le>Suc (getn (payload ml)) . PX n (payload ml) \<and> get_cond (payload ml) = Some False"
                    using Nnew_leq' Nnew_spec by auto
    
                  show "safe gs ml" using guardedD[OF Suc.prems(4) Hpay Hcont]
                    by auto
                qed
                

              have G1 : "|gs| {PX ni} [G SwhileC' [body]] @ c'"
                using guardedD[OF Suc.prems(4)] HTE[OF Htrue]
                by auto

            hence G1' : "|gs| {PX (Suc ni - 1)} [G SwhileC' [body]] @ c'"
              by auto

            have Ggood : "|gs| {PX (Suc ni)} [body] @ [G SwhileC' [body]] @ c'"
              using HTE[OF Htrue G1'] HTE[OF Htrue] by auto

            have Almost :  "safe gs m2" using guardedD[OF Ggood M'] Mp2'_cont
              by auto

            show "safe gs m" 
            proof
              fix mfin

              assume "sem_exec_p gs m mfin"
              then show "imm_safe gs mfin" unfolding sem_exec_p_def
              proof(cases rule: rtranclp.cases)
                case rtrancl_refl
                then have "sem_step_p gs mfin m'" using Inl unfolding sem_step_p_eq by auto
                then show ?thesis unfolding imm_safe_def by blast
              next
                case (rtrancl_into_rtrancl b)

                have Step : "sem_step_p gs m m'" using Inl unfolding sem_step_p_eq by auto
                have Steps : "sem_exec_p gs m' mfin" using rtranclp_bisect1[OF sem_step_determ rtrancl_into_rtrancl(1) Step rtrancl_into_rtrancl(2)] unfolding sem_exec_p_def
                  by auto
                show ?thesis using safeD[OF Almost Steps] by auto

    qed


(* Now, to finish the argument, we need to show that terminating programs will always have a maximum number of 
fuel they consume before they terminate, and that nonterminating programs are safe anyway.

so, we can use this maximum fuel as an upper bound for ni, and we should be done. *)

end