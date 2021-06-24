theory ImpCtl
  imports "../Gensyn" "../Gensyn_Descend" "../Mergeable/Mergeable" "../Mergeable/MergeableInstances"
          "../Lifting/LiftUtils" "../Lifting/LiftInstances"
          "../Lifting/AutoLift" "../Hoare/Hoare_Ghost" "../Hoare/CPS_Hoare_Step" "../Lifting/LangCompFull"
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
  assumes P1_valid : "\<And> st g.  P1 st g \<Longrightarrow> get_cond st \<noteq> None"
  assumes P2_valid : "\<And> st g . P2 st g \<Longrightarrow> get_cond st \<noteq> None"

  assumes Hcond : "|gs| {-R1-} {= P1 =} [cond] {= P2 =}"
  assumes Htrue : "|gs| {-R2-} {= (\<lambda> st g . P2 st g \<and> get_cond st = Some True) =} [body]
                        {= P3 =}"
  assumes Hfalse : "|gs| {-R2-} {= (\<lambda> st g . P2 st g \<and> get_cond st = Some False) =} [] {=P3=}"
  shows "|gs| {-(R1 OO R2)-} {= P1 =} [G Sif' [cond, body]] {= P3 =}"
proof
  fix c'
  fix g g''

  assume R: "(R1 OO R2) g g''"

  assume Guard : "|gs| {P3} g'' c'"

  obtain g' where G'1 : "R1 g g'" and G'2 : "R2 g' g''"
    using R unfolding OO_def by blast

(* need to think about how we are structuring states. *)
(* where will the data of interest be *)
  have Gtrue : "|gs| {\<lambda>st gx. P2 st gx \<and> get_cond st = Some True} g' ([body] @ c')"
    using HTE[OF Htrue G'2 Guard] by auto

  have Gfalse : "|gs| {\<lambda>st gx. P2 st gx \<and> get_cond st = Some False} g' ([] @ c')"
    using HTE[OF Hfalse G'2 Guard] by auto

  show "|gs| {P1} g ([G Sif' [cond, body]] @ c')"
  proof
    fix m :: "('a, 'b) state"

    assume M : "P1 (payload m) g"
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

      hence P1sm' : "P1 (payload m') g" using M unfolding Sm' by auto

      (* next: step to the end of cond. *)

      have Sub : "|gs| {P2} g' ([G Sif' [body]] @ c')"
      proof
        fix mp2 :: "('a, 'b) state"

        assume MP2 : "P2 (payload mp2) g'"

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

            have Mp2'_p2 : "P2 (payload mp2') g'"
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

              have Mp2'_p2_true :  "P2 (payload mp2') g' \<and> get_cond (payload mp2') = Some True"
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

              have Mp2'_p2_false :  "P2 (payload mp2') g' \<and> get_cond (payload mp2') = Some False"
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

      have Guard' : "|gs| {P1} g ([cond] @ ([G Sif' [body]] @ c'))"
        using HTE[OF Hcond G'1 Sub] by auto

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
*)

(* TODO: I think finiteness is necessary, but there is probably
a way to avoid this requirement if we introduce ghost variables or similar
(the reason it arises is that we need to pick a single fuel bound
for the entire state space (of terminating executions), but this is
possible only if the state is finite (?)
*)

definition ridem :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"ridem R \<equiv> ((R OO R) = R)"

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
  (* is this correct? *)
  assumes Htrue : "|gs| {-(\<lambda> g g' . g' = g - 1)-} {=(\<lambda> st g . PX g st) =} [body] {=(\<lambda> st g . PX g st) =}"
  assumes PX_P1 : "\<And> n st . PX n st \<Longrightarrow> P1 st"
  assumes P1_PX : "\<And> st . P1 st \<Longrightarrow> PX (getn st) st"
  assumes PX_closed : "\<And> n st . PX n st \<Longrightarrow> PX (n + 1) st"
  assumes Donefor : "\<And> stx c . PX 0 (payload stx) \<Longrightarrow> s_cont stx = Inl ([G SwhileC' [body]] @ c) \<Longrightarrow> safe gs stx"
(* next thing to try: rewrite this to g = g', and then constrain in conclusion (this way it looks more like original *)
(* also look at where the last proof in ImpCtl.thy goes wrong. *)
  shows "|gs| {- (\<lambda> (g :: nat) g' . (g' = g)) -} {= (\<lambda> st g . g = getn st \<and> PX g st)  =} [G SwhileC' [body]] {= (\<lambda> st g . (\<exists> n . n \<le> g \<and> PX n st \<and> get_cond st = Some False)) =}"
proof
  fix c'

  fix g g' :: nat

  assume Gleq : "g'=g"

  assume Guard : "|gs| {\<lambda>st g. \<exists>n\<le>g. PX n st \<and> get_cond st = Some False} g' c'"

  show "|gs| {\<lambda>st g. g = getn st \<and> PX g st} g ([G SwhileC' [body]] @ c')" 
    using Gleq Guard
  proof(induction g arbitrary: g' c')
    case 0
    show ?case
    proof
      fix m :: "('a, 'b) state"
      assume Hm : "0 = getn (payload m) \<and> PX 0 (payload m)"
      then have Hm' : "PX 0 (payload m)" by auto

      assume Hcontm : "s_cont m = Inl ([G SwhileC' [body]] @ c')" 
      show "safe gs m" using Donefor[OF Hm' Hcontm] by auto
    qed
  next
    case (Suc g)
    show ?case 
    proof
      fix m :: "('a, 'b) state"
      assume Hm : "Suc g = getn (payload m) \<and> PX (Suc g) (payload m)" 
      then have Pay : "Suc g = getn (payload m)" and Px : "PX (Suc g) (payload m)"
        by auto

      assume Hcontm : "s_cont m = Inl ([G SwhileC' [body]] @ c')" 
      show  "safe gs m" 

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
  
        have M_P1 : "PX (Suc g) (payload m)" using Px Hcontm by auto
  
        have M'_valid : "\<And> p . fst (payload m) \<noteq> mdp p None" using PX_valid[OF M_P1]
          by(auto simp add: get_cond_def split:prod.splits)
  
        have Sm' : "payload m = payload m'"
          using Hcontm Hsyn F_eq M'_valid  unfolding HF
          by(cases m; cases m'; auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
             schem_lift_defs 
            merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
            split: md_prio.splits md_triv.splits option.splits)
  
        have M' : "PX (Suc g) (payload m')" using Sm' M_P1 by auto

        show "safe gs m"
        proof(cases "get_cond (payload m)")
          case None
  
          then have False using PX_valid[OF M_P1]
            by(auto simp add: get_cond_def split: prod.splits md_prio.splits md_triv.splits option.splits)
          then show ?thesis by auto
  
        next
          case Some' : (Some cnd)

          have Haa : "|gs| {\<lambda>st g. \<exists>n\<le>g. PX n st \<and> get_cond st = Some False} g c'"
          proof
            fix ml :: "('a, 'b) state"
            assume Hpay : "\<exists>n\<le>g . PX n (payload ml) \<and> get_cond (payload ml) = Some False"
            assume Hcont : "s_cont ml = Inl c'"

            obtain nnew where Nnew_leq  : "nnew \<le> g" and Nnew_spec : "PX nnew (payload ml) \<and> get_cond (payload ml) = Some False"
              using Hpay by auto

            have Nnew_leq' : "nnew \<le> Suc g" using Nnew_leq by auto

            have Hpay' : "\<exists>n\<le>g' . PX n (payload ml) \<and> get_cond (payload ml) = Some False"
              using Nnew_leq' Nnew_spec Suc.prems by auto

            show "safe gs ml" using guardedD[OF Suc.prems(2) Hpay' Hcont]
              by auto
          qed

          show ?thesis
          proof(cases cnd)
            case True

            have Mp2'_cont : "s_cont m' = Inl ([body, G SwhileC' [body]] @ c')" sorry

            have G1 : "|gs| {\<lambda>st g. g = getn st \<and> PX g st} g ([G SwhileC' [body]] @ c')"
              using Suc.IH[OF refl Haa]
              by auto

            hence G1' : "|gs| {\<lambda>st g. g = getn st \<and> PX g st} (Suc g - 1) ([G SwhileC' [body]] @ c')"
              by auto

(*
            have Htrue' : "|gs| {-(\<lambda> g g' . g' = g - 1)-} {=(\<lambda> st g . PX g st) =} [body] {=(\<lambda> st g . g = getn st \<and> PX g st) =}"
            proof
              fix c'' 
              fix gx gx' :: nat
              assume Gx : "gx' = gx - 1"
              assume "|gs| {\<lambda>st g. g = getn st \<and> PX g st} gx' c''"

              show "|gs| {\<lambda>st g. PX g st} gx ([body] @ c'')"
                using HTE[OF Htrue Gx]
*)
            have Ggood : "|gs| {\<lambda>st g. PX g st} (Suc g)  ([body] @ [G SwhileC' [body]] @ c')"
              using  (*HTE[OF Htrue' _ G1, of "Suc g"] Htrue by auto *)
HTE[OF Htrue]


            have Almost :  "safe gs m'" using guardedD[OF Ggood M'] Mp2'_cont
              by auto

            show "safe gs m" using
            proof
              fix mfin


            then show ?thesis sorry
          next
            case False
            then show ?thesis sorry
          qed

  qed


    fix m :: "('a, 'b) state"
    assume "g = getn (payload m) \<and> PX g (payload m)"
    hence Pg : "PX g (payload m)" and Getn_g : "getn (payload m) = g" by auto
    assume Hc : "s_cont m = Inl ([G SwhileC' [body]] @ c')"
  
    show "safe gs m"
(*
      proof(cases "(sem_step gs m)")
        case (Inr bad)
  
        then have False using Hc H0
          by(auto simp add: sem_step_def)
  
        then show ?thesis by auto
      next
        case (Inl m')
  
        have F_eq : "sem_step \<lparr> s_sem = f \<rparr> m = Inl m'"
          using sym[OF dominant_pcomps'[OF Hpres Hnemp Hdom]] Hc Inl H0
          by(simp add: sem_step_def)
  
        have M_P1 : "PX ( g) (payload m)" using Pg Hc by auto
  
        have M'_valid : "\<And> p . fst (payload m) \<noteq> mdp p None" using PX_valid[OF M_P1]
          by(auto simp add: get_cond_def split:prod.splits)
  
        have Sm' : "payload m = payload m'"
          using Hc Hsyn F_eq M'_valid  unfolding HF
          by(cases m; cases m'; auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
             schem_lift_defs 
            merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
            split: md_prio.splits md_triv.splits option.splits)
  
        have M' : "PX (g) (payload m')" using Sm' M_P1 by auto
  
        show "safe gs m"
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

            have Mp2'_cont : "s_cont m' = Inl ([body, G SwhileC' [body]] @ c')" sorry

            show "safe gs m" using HTE[OF Htrue TrueI]
(* problem, as before: what if g' = Suc gi? *)

            have G1 : "|gs| {\<lambda>st gx.  getn st \<le> gx \<and> PX gx st} (g) ([G SwhileC' [body]] @ c')"
              using 
              by auto

            hence G1' : "|gs| {\<lambda>st gx.  gx = getn st \<and> PX gx st} (Suc gi - 1) ([G SwhileC' [body]] @ c')"
              by auto
*)
    using Guard Gleq Pg Getn_g Hc
  proof(induction g arbitrary: g' c' m)
    case 0
    have "imm_safe gs m" using 0
      apply(cases "sem_step gs m")
       apply(auto simp add: sem_step_def imm_safe_def sem_step_p_eq)
      done

  next
    case (Suc gi)
    show ?case
    proof(cases "(sem_step gs m)")
      case (Inr bad)

      then have False using Suc.prems H0
        by(auto simp add: sem_step_def)

      then show ?thesis by auto
    next
      case (Inl m')

      have F_eq : "sem_step \<lparr> s_sem = f \<rparr> m = Inl m'"
        using sym[OF dominant_pcomps'[OF Hpres Hnemp Hdom]] Suc.prems Inl H0
          by(simp add: sem_step_def)
  
        have M_P1 : "PX (Suc gi) (payload m)" using Suc.prems by auto
  
        have M'_valid : "\<And> p . fst (payload m) \<noteq> mdp p None" using PX_valid[OF M_P1]
          by(auto simp add: get_cond_def split:prod.splits)
  
        have Sm' : "payload m = payload m'"
          using Suc.prems Hsyn F_eq M'_valid  unfolding HF
          by(cases m; cases m'; auto simp add: s_cont_def sem_step_def imp_sem_l_gen_def imp_ctl_sem_def imp_sem_lifting_gen_def
             schem_lift_defs 
            merge_l_def fst_l_def snd_l_def prio_l_def triv_l_def option_l_def LNew_def
            split: md_prio.splits md_triv.splits option.splits)
  
        have M' : "PX (Suc gi) (payload m')" using Sm' M_P1 by auto

        show "safe gs m"
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

            have Mp2'_cont : "s_cont m' = Inl ([body, G SwhileC' [body]] @ c')" sorry


            have Hmm : "|gs| {\<lambda>st g. PX g st \<and> get_cond st = Some False} (g'-1) c'" 
            proof
              fix ml :: "('a, 'b) state"

              assume 0 : "PX (g' - 1) (payload ml) \<and> get_cond (payload ml) = Some False"
              assume 1: "s_cont ml = Inl c'"

              have Boo : "PX (g' - 1) (payload ml)" using 0 by auto

              show "safe gs ml" using Suc.prems Suc.IH HTE[OF Htrue]
(*
              proof(cases g')
                case 0
                then show ?thesis using Donefor
              next
                case (Suc nat)
                then show ?thesis sorry
              qed
*)

            have IHR : "|gs| {\<lambda>st g. g = getn st \<and> PX g st} gi ([G SwhileC' [body]] @ c')"
              using Suc.IH[OF Hmm] Suc.prems by auto

            show ?thesis using HTE[OF Htrue, of "Suc gi" "gi"]
            proof(cases "g' = Suc gi")

              show "safe gs m" using Suc.prems Suc.IH
        

(* problem, as before: what if g' = Suc gi? *)

            have G1 : "|gs| {\<lambda>st gx.  getn st \<le> gx \<and> PX gx st} (gi) ([G SwhileC' [body]] @ c')"
              using Suc.IH[OF ] Suc.prems HTE[OF Htrue]
              by auto

            hence G1' : "|gs| {\<lambda>st gx.  gx = getn st \<and> PX gx st} (Suc gi - 1) ([G SwhileC' [body]] @ c')"
              by auto

(*
            have G1'' : "|gs| {\<lambda>st gx. PX gx st} (Suc gi - 1) ([G SwhileC' [body]] @ c')"
            proof
*)
            have Ggood : "|gs| {\<lambda>st gx.  gx = getn st \<and> PX gx st} (Suc gi) ([body] @ [G SwhileC' [body]] @ c')"
              using HTE[OF Htrue] Suc.prems by auto

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

            have Mp2'_cont : "s_cont m' = Inl (c')" sorry

            show "safe gs m" using guardedD[OF ] Suc.prems

          qed
        qed
      qed
    qed
  qed
qed


end