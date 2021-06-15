theory ImpCtl
  imports "../Gensyn" "../Gensyn_Descend" "../Mergeable/Mergeable" "../Mergeable/MergeableInstances"
          "../Lifting/LiftUtils" "../Lifting/LiftInstances"
          "../Lifting/AutoLift" "../Hoare/CPS_Hoare" "../Hoare/CPS_Hoare_Step" "../Lifting/LangCompFull"
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
         | _ \<Rightarrow> [] \<comment> \<open> error \<close>))
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

(* failed experiments in trying to coax the auto-lifter *)

(*
definition imp_sem_l :: "syn \<Rightarrow> 'x state \<Rightarrow> 'x state" where
"imp_sem_l =
  lift_map_s imp_trans
    (schem_lift (SP NA (SP NB NC))
                (SP (SPRC imp_prio (SO NA)) (SP (SPRK (SO NB)) (SPRK (SO NC)))))
  imp_ctl_sem"
*)
(*
definition imp_sem_lifting_gen_huh ::  "(ImpCtl.syn', 'x gensyn list * int, 
                                      ('a :: Pordb ) *
                                      ('x gensyn list md_triv option md_prio * int md_triv option md_prio)) lifting" where
"imp_sem_lifting_gen_huh = 
 (schem_lift (SP NA NB) (SP NX (SP (SPRI (SO NA)) (SPRI (SO NB)))))"
*)

(*
definition imp_sem_lifting_gen_huh ::  "(ImpCtl.syn', 'x gensyn list, 
                                      ('x gensyn list md_triv option md_prio * 
                                           ('a :: Pordb ))) lifting" where
"imp_sem_lifting_gen_huh = 
 (schem_lift NA (SP (SPRI (SO NA)) NX))"
*)



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

lemma HWhile_gen :
  assumes H0 : "gs = \<lparr> s_sem = pcomps' fs \<rparr>"
  (*assumes H1 : "seq_sem_l_gen lfts \<in> set fs" *)
  assumes HF : "f = imp_sem_l_gen lfts"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hnemp : "g \<in> set fs"
  assumes Hdom : "(f \<downharpoonleft> (set fs) Swhile')"
  assumes Hsyn : "lfts Swhile' = Swhile"
  (* TODO: generalize. these should be expressed using valid-sets *)
  assumes P1_valid : "\<And> st.  P1 st \<Longrightarrow> get_cond st \<noteq> None"
  assumes P2_valid : "\<And> st.  P2 st \<Longrightarrow> get_cond st \<noteq> None"
  assumes Hcond : "|gs| {- P1 -} [cond] {- P1 -}"
  assumes Htrue : "|gs| {- (\<lambda> st . P1 st \<and> get_cond st = Some True) -} [body]
                        {- P1 -}"
(*
  assumes Hfalse : "\<And> st . P2 st \<and> get_cond st = Some False \<Longrightarrow> P1 st" 
*)
  shows "|gs| {- P1 -} [G Swhile' [cond, body]] {- (\<lambda> st . P1 st ) -}"
proof
  fix c'
  assume Guard : "|gs| {\<lambda>st. P1 st  } c'"

  have Gtrue : "|gs| {\<lambda>st. P1 st \<and> get_cond st = Some True} [body] @ c'"
    using HTE[OF Htrue Guard]
    
    by auto

  have Hc' : "|gs| {-  \<lambda>st. P1 st \<and> get_cond st = Some True -} [cond] {- P1 -}"
    using HConseq[OF Hcond, of "\<lambda>st. P1 st \<and> get_cond st = Some True" "P1"]
    by auto

  have Gcond : "|gs| {P1} [cond] @ c'" using HTE[OF Hcond Guard] by auto

  have Gtrue' : "|gs| {\<lambda>st. P1 st \<and> get_cond st = Some True} [body, cond] @ c'"
    using HTE[OF Htrue Gcond] by auto

  have Test : "\<And> c' . 
|gs| {\<lambda> st . P1 st \<and> get_cond st = Some True}  [body, G Swhile' [cond, body]]  @ c' \<Longrightarrow>
|gs| { P1 } [cond, G Swhile' [cond, cond, body]] @ c' \<Longrightarrow>
|gs| {P1} ([G Swhile' [cond, body]] @ c')"
  proof
    fix c' 
    fix m :: "('a, 'b) state"

    assume A0 : "|gs| {\<lambda> m . P1 m \<and> get_cond m = Some True} [body, G Swhile' [cond, body]] @ c'"
    assume A1 : "|gs| {P1} [cond, G Swhile' [cond, cond, body]] @ c'"
    assume Pay : "P1 (payload m)"
    assume Cont : "s_cont m = 
      Inl ([G Swhile' [cond, body]] @ c')"

    show "safe gs m"
    proof
      fix m'
      assume Exc : "sem_exec_p gs m m'"

      obtain n where N: "sem_exec_c_p gs m n m'"
        using exec_p_imp_exec_c_p[OF Exc] by auto

      show "imm_safe gs m'" using N A0 A1 Pay Cont unfolding sem_exec_p_def
      proof(induction arbitrary: c'  rule: sem_exec_c_p.induct)
        case (Excp_0 mx)
        then show ?case 
        proof(cases "sem_step gs mx")
          case (Inr bad)
          then have False using Excp_0
            by(auto simp add: sem_step_def)
          thus ?thesis by auto
        next
          case (Inl m')

          have F_eq : "sem_step \<lparr> s_sem = f \<rparr> mx = Inl m'"
            using sym[OF dominant_pcomps'[OF Hpres Hnemp Hdom]] Excp_0 Inl H0
            by(simp add: sem_step_def)

          have "sem_step gs mx = Inl m'" 
            using Hsyn H0 F_eq Inl unfolding HF
            by(cases m'; auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
           schem_lift_defs 
            merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
            split: md_prio.splits md_triv.splits option.splits)

          thus ?thesis
            unfolding imm_safe_def sem_step_p_eq by blast
        qed
      next
        case (Excp_Suc m1 m2 n m3)
        then show ?case 
        proof(cases "sem_step gs m1")
          case (Inr bad)
          then have False using Excp_Suc
            by(auto simp add: sem_step_def)
          thus ?thesis by auto
        next
          case (Inl m1')

          have F_eq : "sem_step \<lparr> s_sem = f \<rparr> m1 = Inl m1'"
            using sym[OF dominant_pcomps'[OF Hpres Hnemp Hdom]] Excp_Suc Inl H0
            by(simp add: sem_step_def)

          have Step1 : "sem_step gs m1 = Inl m1'" 
            using Hsyn H0 F_eq Inl unfolding HF
            by(auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
           schem_lift_defs 
            merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
            split: md_prio.splits md_triv.splits option.splits)

          have Meq : "m1' = m2" using Excp_Suc.hyps Inl unfolding sem_step_p_eq by auto

          have Cont1' : "s_cont m2 = Inl ([cond, G Swhile' [cond, cond, body]] @ c')"
            using Hsyn H0 F_eq Inl Excp_Suc.prems Meq unfolding HF
            by(cases m1; auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
           schem_lift_defs 
            merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
            split: md_prio.splits md_triv.splits option.splits prod.splits)

          have P1' : "P1 (payload m2)"
            using Hsyn H0 F_eq Inl Excp_Suc.prems Meq  P1_valid[OF Excp_Suc.prems(3)] unfolding HF
            by(cases m1; cases m2; 
                auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
                schem_lift_defs 
                merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
                get_cond_def
                split: md_prio.splits md_triv.splits option.splits)

          show ?thesis
            using Excp_Suc.IH[OF Excp_Suc.prems(1) ]  Excp_Suc.prems

          proof(cases "sem_step gs m1'")
            case Inr' : (Inr bad)
            then have False using Excp_Suc Cont1'
              by(auto simp add: sem_step_def)
            thus ?thesis by auto
          next
            case Inl' : (Inl m1'')
            have F_eq : "sem_step \<lparr> s_sem = f \<rparr> m1' = Inl m1''"
              using sym[OF dominant_pcomps'[OF Hpres Hnemp Hdom]] Excp_Suc Inl H0 Inl
              by(simp add: sem_step_def)
  
            have Step1 : "sem_step gs m1 = Inl m1'" 
              using Hsyn H0 F_eq Inl unfolding HF
              by(auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
             schem_lift_defs 
              merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
              split: md_prio.splits md_triv.splits option.splits)
  
            have Cont1' : "s_cont m1' = Inl ([cond, G Swhile' [cond, cond, body]] @ c')"
              using Hsyn H0 F_eq Inl Excp_Suc.prems unfolding HF
              by(cases m1; auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
             schem_lift_defs 
              merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
              split: md_prio.splits md_triv.splits option.splits prod.splits)



            unfolding imm_safe_def sem_step_p_eq by blast
        qed

        qed
*)
(*
  have 0: "|gs| {\<lambda>st. P2 st \<and> get_cond st = Some False} [body] @ c'"
    using HTE[OF Hcond'] by auto
*)
  show "|gs| {P1} [G Swhile' [cond, body]] @ c'"
  proof
    fix m :: "('a, 'b) state"

    assume M : "P1 (payload m)"
    assume CM : "s_cont m = Inl ([G Swhile' [cond, body]] @ c')"


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

      have CM' : "s_cont m' = Inl ([cond] @ ([ G Swhile' [cond, cond, body]] @ c'))" 
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

      have Sub : "|gs| {P1} [ G Swhile' [cond, cond, body]] @ c'"
      proof
        fix mp2 :: "('a, 'b) state"

        assume MP2 : "P1 (payload mp2)"

        assume Cont2 : "s_cont mp2 = Inl ([G Swhile' [cond, cond, body]] @ c')"

        show "safe gs mp2"
        proof(cases "get_cond (payload mp2)")
          case None

          then have False using P1_valid[OF MP2]
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

            have Mp2'_p2 : "P1 (payload mp2')"
              using Cont2 Hsyn H0 MP2 F_eq' P1_valid[OF MP2] Some' unfolding HF
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
                using Cont2 Hsyn H0 MP2 F_eq' P1_valid[OF MP2] True Some' unfolding HF
                by(cases mp2; cases mp2'; 
                    auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
                    schem_lift_defs 
                    merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
                    get_cond_def
                    split: md_prio.splits md_triv.splits option.splits)

              have Mp2'_p2_true :  "P1 (payload mp2') \<and> get_cond (payload mp2') = Some True"
                using Mp2'_p2 Mp2'_cond
                by auto

              have Mp2'_cont : "s_cont mp2' = Inl ([body] @ G Swhile' [cond, body] # c')"
                using Cont2 Hsyn H0 MP2 F_eq' P1_valid[OF MP2] True Some' unfolding HF
                by(cases mp2; cases mp2'; 
                    auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
                    schem_lift_defs 
                    merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
                    get_cond_def
                    split: md_prio.splits md_triv.splits option.splits)

              have Mp2'_safe : "safe gs mp2'"
                using HTE[OF Htrue] guardedD[OF Gtrue']

(*
              proof
                fix mend :: "('a, 'b) state"

                assume Exec : "sem_exec_p gs mp2' mend" 
                show "imm_safe gs mend"
*)
                using guardedD[OF Guard]


      show "safe gs m"
        using HTE[OF Hcond] HTE[OF Htrue]
(*

      show "safe gs m"
      proof(cases "get_cond (payload m')")
        case None

        then have False using P1_valid[OF P1sm'] by auto

        then show ?thesis by auto
      next
        case (Some cond)
        show ?thesis
        proof(cases cond)
            case False

            have Mp2'_cond : "get_cond (snd mp2') = Some False" 
              using Cont2 Hsyn H0 MP2 F_eq' P2_valid[OF MP2] False Some' unfolding HF
              by(cases mp2; cases mp2'; 
                  auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
                  schem_lift_defs 
                  merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
                  get_cond_def
                  split: md_prio.splits md_triv.splits option.splits)

            have Mp2'_p2_false :  "P2 (snd mp2') \<and> get_cond (snd mp2') = Some False"
              using Mp2'_p2 Mp2'_cond
              by auto

            have Mp2'_cont : "s_cont mp2' = [] @ c'"
              using Cont2 Hsyn H0 MP2 F_eq' P2_valid[OF MP2] False Some' unfolding HF
              by(cases mp2; cases mp2'; 
                  auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
                  schem_lift_defs 
                  merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
                  get_cond_def
                  split: md_prio.splits md_triv.splits option.splits)

            have Mp2'_safe : "safe gs mp2'"
              using guardedD[OF Guard Mp2'_p2_false] Mp2'_cont
              by auto
*)
            show ?thesis
            proof
              fix mz
              assume Exec : "sem_exec_p gs mp2 mz"

              show "imm_safe gs mz" using Exec unfolding sem_exec_p_def
              proof(cases rule: rtranclp.cases)
                case rtrancl_refl

                then have "(\<exists>m'. sem_step gs mz = Some m')"
                  using Some'' unfolding imm_safe_def sem_step_p_eq
                  by(cases mp2'; auto)

                then show ?thesis unfolding imm_safe_def sem_step_p_eq by auto
              next
                case (rtrancl_into_rtrancl b)

                have Step : "sem_step_p gs mp2 mp2'" using Some''
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

    have Guard' : "|gs| {P1} [cond] @ ([G Swhile' [body]] @ c')"
      using HTE[OF Hcond Sub] by auto

    have Safe' : "safe gs m'" using guardedD[OF Guard' P1sm' CM'] by auto

    show "safe gs m"
    proof
      fix mz

      assume Z: "sem_exec_p gs m mz"

      then show "imm_safe gs mz" unfolding sem_exec_p_def
      proof(cases rule: rtranclp.cases)
        case rtrancl_refl

        then have "(\<exists>m'. sem_step gs mz = Some m')"
          using Some unfolding imm_safe_def sem_step_p_eq
          by(cases m'; auto)

        then show ?thesis using Some unfolding imm_safe_def sem_step_p_eq
          by(auto)
      next
        case (rtrancl_into_rtrancl b)

        have Step : "sem_step_p gs m m'" using Some
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