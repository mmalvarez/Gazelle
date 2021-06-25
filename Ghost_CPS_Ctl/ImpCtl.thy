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
  (* is this correct? maybe we can either use different getn functions between body and conclusion,
     or else not need getn in conclusion of Htrue premise. Or both...*)
  assumes Htrue : "|gs| {-(\<lambda> g g' . g' = g - 1)-} {=(\<lambda> st g . getn st \<ge> g \<and> PX g st) =} [body] {=(\<lambda> st g . getn st \<ge> g \<and> PX g st) =}"
(*  assumes Htrue' : "|gs| {-(\<lambda> g g' . g' = g)-} {=(\<lambda> st g . g = getn st \<and> P g st) =} [body] {= (\<lambda> st g . PX (g - 1) st)=}" *)
  assumes PX_P1 : "\<And> n st . PX n st \<Longrightarrow> P1 st"
  assumes P1_PX : "\<And> st . P1 st \<Longrightarrow> PX (getn st) st"
  assumes Donefor : "\<And> stx c . PX 0 (payload stx) \<Longrightarrow> s_cont stx = Inl ([G SwhileC' [body]] @ c) \<Longrightarrow> safe gs stx"
(* next thing to try: rewrite this to g = g', and then constrain in conclusion (this way it looks more like original *)
(* also look at where the last proof in ImpCtl.thy goes wrong. *)
(* TODO: do we really need "getn st \<le> g" in conclusion? *)
  shows "|gs| {- (\<lambda> (g :: nat) g' . (g' = g)) -} {= (\<lambda> st g . getn st \<ge> g \<and> PX g st)  =} [G SwhileC' [body]] {= (\<lambda> st g .  (\<exists> n . n \<le> g \<and> PX n st \<and> get_cond st = Some False)) =}"
(* removed from last clause of conclusion: getn st \<le> g \<and> *)
proof
  fix c'

  fix g g' :: nat

  assume Gleq : "g'=g"

  assume Guard : "|gs| {\<lambda>st g. (\<exists>n\<le>g. PX n st \<and> get_cond st = Some False)} g' c'"

  show "|gs| {\<lambda>st g. getn st \<ge> g \<and> PX g st} g ([G SwhileC' [body]] @ c')" 
    using Gleq Guard
  proof(induction g arbitrary: g' c')
    case 0
    show ?case
    proof
      fix m :: "('a, 'b) state"
      assume Hm : "getn (payload m) \<ge> 0 \<and> PX 0 (payload m)"
      then have Hm' : "PX 0 (payload m)" by auto

      assume Hcontm : "s_cont m = Inl ([G SwhileC' [body]] @ c')" 
      show "safe gs m" using Donefor[OF Hm' Hcontm] by auto
    qed
  next
    case (Suc g)
    show ?case 
    proof
      fix m :: "('a, 'b) state"
      assume Hm : "getn (payload m) \<ge> Suc g \<and> PX (Suc g) (payload m)" 
      then have Pay : "getn (payload m) \<ge> Suc g " and Px : "PX (Suc g) (payload m)"
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

        have M'_full : "getn (payload m') \<ge> Suc g \<and> PX (Suc g) (payload m')" using  Sm' Hm by auto

        show "safe gs m"
        proof(cases "get_cond (payload m)")
          case None
  
          then have False using PX_valid[OF M_P1]
            by(auto simp add: get_cond_def split: prod.splits md_prio.splits md_triv.splits option.splits)
          then show ?thesis by auto
  
        next
          case Some' : (Some cnd)

          have Haa : "|gs| {\<lambda>st g.  (\<exists>n\<le>g. PX n st \<and> get_cond st = Some False)} g c'"
          proof
            fix ml :: "('a, 'b) state"
            assume Hpay : "(\<exists>n\<le>g . PX n (payload ml) \<and> get_cond (payload ml) = Some False)"
            assume Hcont : "s_cont ml = Inl c'"

            obtain nnew where Nnew_leq  : "nnew \<le> g" and Nnew_spec : "PX nnew (payload ml) \<and> get_cond (payload ml) = Some False"
              using Hpay by auto

            have Nnew_leq' : "nnew \<le> Suc g" using Nnew_leq by auto

            have Hpay' : " (\<exists>n\<le>g' . PX n (payload ml) \<and> get_cond (payload ml) = Some False)"
              using Nnew_leq' Nnew_spec Suc.prems Hpay by auto

            show "safe gs ml" using guardedD[OF Suc.prems(2) Hpay' Hcont]
              by auto
          qed

          show ?thesis
          proof(cases cnd)
            case True

            have Mp2'_cont : "s_cont m' = Inl ([body, G SwhileC' [body]] @ c')" sorry

            have G1 : "|gs| {\<lambda>st g. getn st \<ge> g \<and> PX g st} g ([G SwhileC' [body]] @ c')"
              using Suc.IH[OF refl Haa] 
              by auto

            hence G1' : "|gs| {\<lambda>st g. getn st \<ge> g \<and> PX g st} (Suc g - 1) ([G SwhileC' [body]] @ c')"
              by auto

            have Ggood : "|gs| {\<lambda>st g. getn st \<ge> g \<and> PX g st} (Suc g) ([body] @ [G SwhileC' [body]] @ c')" using HTE[OF Htrue _ G1', of "Suc g"] by auto

            have Almost :  "safe gs m'" using guardedD[OF Ggood M'_full] Mp2'_cont
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

(*
            have Haa' : "|gs| {\<lambda>st g. getn st \<le> g \<and> (\<exists>n\<le>g. PX n st \<and> get_cond st = Some False)} g c'"  
            proof
              fix ml :: "('a, 'b) state"
              assume Hpay : "getn (payload ml) \<le> g \<and> (\<exists>n\<le>g . PX n (payload ml) \<and> get_cond (payload ml) = Some False)"
              assume Hcont : "s_cont ml = Inl c'"
    
  
              show "safe gs ml" using guardedD[OF Suc.prems(2) ] Suc.prems
                by auto
            qed
*)

            have M'_full' : "(\<exists>n\<le>g'. PX n (payload m') \<and> get_cond (payload m') = Some False)"
              using M'_full False Some' unfolding Suc.prems(1) Sm'
              by auto

            have Almost : "safe gs m'"
              using guardedD[OF Suc.prems(2) M'_full' Mp2'_cont] by auto

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
          qed
        qed
      qed
    qed
  qed
qed

definition step_limit ::
  "('syn, 'mstate) semc \<Rightarrow> 'syn gensyn list md_triv option md_prio \<times>
      String.literal md_triv option md_prio \<times> 'mstate \<Rightarrow> nat \<Rightarrow> bool" where
"step_limit gs m n =
  ((\<exists> m' . sem_exec_c_p gs m n m' \<and> s_cont m' = Inl []) \<or>
   (n = 0 \<and> (\<forall> n' m' . sem_exec_c_p gs m n' m' \<longrightarrow> s_cont m' \<noteq> (Inl []))))"

lemma step_limit_unique :
  shows "\<exists>! n . step_limit gs st n"
proof(cases "\<exists> n st' . sem_exec_c_p gs st n st' \<and> s_cont st' = Inl []")
  case True

  then obtain n st' where True1 : "sem_exec_c_p gs st n st'" and True2: "s_cont st' = Inl []"
    by auto

  show ?thesis
  proof
    show "step_limit gs st n" unfolding step_limit_def using True1 True2 by blast
  next
    fix na
    assume Bad : "step_limit gs st na"

    obtain sta where Sta1 : "sem_exec_c_p gs st na sta" and Sta2 : "s_cont sta = Inl []"
      using True Bad unfolding step_limit_def
      by(blast)

    show "na = n"
    proof(cases "na < n")
      case Lt : True

      obtain st'_alt where Uhoh1 : "sem_exec_c_p gs st na st'_alt" and Uhoh2 : "sem_exec_c_p gs st'_alt (n - na) st'"
        using exec_c_p_split[OF True1, of na] Lt by auto

      have Steq : "st'_alt = sta" using exec_c_p_determ[OF Sta1 Uhoh1] by auto

      (* fairly straigtforward from here. n - na \<ge>1 so we must take a step but can't. so we are done. *)

      then show ?thesis sorry
    next
      case Nlt : False
      then show ?thesis
      proof(cases "n < na")
        case Gt : True

        obtain st'_alt where Uhoh1 : "sem_exec_c_p gs st n st'_alt" and Uhoh2 : "sem_exec_c_p gs st'_alt (na - n) sta"
          using exec_c_p_split[OF Sta1, of n] Gt by auto
  
        have Steq : "st'_alt = st'" using exec_c_p_determ[OF True1 Uhoh1] by auto

        then show ?thesis sorry
      (* fairly straigtforward from here. na - n \<ge>1 so we must take a step but can't. so we are done. *)

      next
        case Ngt : False
        thus ?thesis using Nlt by auto
      qed
    qed
  qed
(* idea: show cases greater than, equal to, less than
zero may have to be psecial cased *)
      
next
  case False

  have Cont' : "step_limit gs st 0" using False
    unfolding step_limit_def
    by blast

  show ?thesis 
  proof
    show "step_limit gs st 0" using Cont' by auto
  next
    fix na
    assume "step_limit gs st na"

    then show "na = 0" using False
      unfolding step_limit_def by blast
  qed
qed

definition step_limit_f ::
  "('syn, 'mstate) semc \<Rightarrow> 'syn gensyn list md_triv option md_prio \<times>
      String.literal md_triv option md_prio \<times> 'mstate \<Rightarrow> nat" where
"step_limit_f gs m = (THE n . step_limit gs m n)"

lemma step_limit_f_step_limit :
  "step_limit gs m (step_limit_f gs m)"
  unfolding step_limit_f_def
  using theI'[OF step_limit_unique, of gs m]
  by auto

lemma step_limit_safe :
  assumes H : "step_limit gs m n"
  assumes Hnz : "n \<noteq> 0"
  shows "safe gs m"
proof
  fix m'
  assume Exec : "sem_exec_p gs m m'"

  obtain n' where N' : "sem_exec_c_p gs m n' m'"
    using exec_p_imp_exec_c_p[OF Exec] by auto

  show "imm_safe gs m'"
  proof(cases "(\<exists> m' . sem_exec_c_p gs m n m' \<and> s_cont m' = Inl [])")
    case True
    then obtain m'x where M'x_exec : "sem_exec_c_p gs m n m'x" and M'x_cont : "s_cont m'x = Inl []"
      by blast

    then show ?thesis 
    proof(cases "n' < n")
      case Lt : True

      obtain m'_alt where
        M'_alt_exec1 : "sem_exec_c_p gs m n' m'_alt" and M'_alt_exec2 : "sem_exec_c_p gs m'_alt (n - n') m'x"
        using exec_c_p_split[OF M'x_exec, of n'] Lt
        by auto

      have M'_eq : "m'_alt = m'" using exec_c_p_determ[OF N' M'_alt_exec1] by auto

      show ?thesis using M'_alt_exec2 unfolding M'_eq
      proof(cases rule: sem_exec_c_p.cases)
        case Excp_0

        hence False using Lt by auto

        then show ?thesis by auto
      next
        case (Excp_Suc m2 n2)

        then show ?thesis unfolding imm_safe_def by blast
      qed
    next
      case False' : False
      then show ?thesis
      proof(cases "n < n'")
        case Gt : True

        obtain m'x_alt where
          M'x_alt_exec1 : "sem_exec_c_p gs m n m'x_alt" and M'x_alt_exec2 : "sem_exec_c_p gs m'x_alt (n' - n) m'"
          using exec_c_p_split[OF N', of n] Gt
          by auto

        have M'x_eq : "m'x_alt = m'x" using exec_c_p_determ[OF M'x_exec M'x_alt_exec1] by auto

        have False using M'x_alt_exec2 unfolding M'x_eq
        proof(cases rule: sem_exec_c_p.cases)
          case Excp_0
          then show ?thesis using Gt by auto
        next
          case (Excp_Suc m2 n2)

          hence "sem_step gs m'x = Inl m2"
            unfolding sem_step_p_eq by auto

          then show ?thesis using M'x_cont
            by(auto simp add: sem_step_def)
        qed

        then show ?thesis by auto
      next
        case Eq : False

        then have Eq' : "n = n'" using False' by auto

        have N'_exec' : "sem_exec_c_p gs m n m'" using N' unfolding Eq' by auto

        have M'_eq : "m' = m'x" using exec_c_p_determ[OF M'x_exec N'_exec'] by auto

        then show ?thesis using M'x_cont unfolding imm_safe_def by auto
      qed
    qed
  next
    case False

    then have False using H Hnz unfolding step_limit_def by blast

    thus ?thesis by auto
  qed
qed
(* "sleekness" of semantics -
idea is that we can't make control-flow decisions based on
priority
*)

definition sleek :: "('syn, 'full, 'mstate) sem \<Rightarrow> bool" where
"sleek gs =
(\<forall> syn st1 st2 . 
  payload st1 = payload st2 \<longrightarrow>
  s_cont st1 = s_cont st2 \<longrightarrow>
  payload (s_sem gs syn st1) = payload (s_sem gs syn st2) \<and>
  s_cont (s_sem gs syn st1) = s_cont (s_sem gs syn st2))"

lemma sleekI :
  assumes "(\<And> syn st1 st2 . 
  payload st1 = payload st2 \<Longrightarrow>
  s_cont st1 = s_cont st2 \<Longrightarrow>
  payload (s_sem gs syn st1) = payload (s_sem gs syn st2) \<and>
  s_cont (s_sem gs syn st1) = s_cont (s_sem gs syn st2))"
  shows "sleek gs" using assms
  unfolding sleek_def by blast

lemma sleekD1 :
  assumes H : "sleek gs"
  assumes H1 : "payload st1 = payload st2"
  assumes H2 : "s_cont st1 = s_cont st2"
  shows "payload (s_sem gs syn st1) = payload (s_sem gs syn st2)" using assms
  unfolding sleek_def
  by blast

lemma sleekD2 :
  assumes H : "sleek gs"
  assumes H1 : "payload st1 = payload st2"
  assumes H2 : "s_cont st1 = s_cont st2"
  shows "s_cont (s_sem gs syn st1) = s_cont (s_sem gs syn st2)" using assms
  unfolding sleek_def
  by blast

lemma sleek_exec :
  assumes H : "sleek gs"
  assumes Hp : "payload st1 = payload st2"
  assumes Hc : "s_cont st1 = s_cont st2"
  assumes H1 : "sem_exec_c_p gs st1 n st1'"
  shows "(\<exists> st2' . sem_exec_c_p gs st2 n st2' \<and> payload st1' = payload st2' \<and>
  s_cont st1' = s_cont st2')"
  using H1 Hc Hp unfolding sem_exec_p_def
proof(induction arbitrary: st2 rule: sem_exec_c_p.induct)
  case (Excp_0 m)

  have Conc' : "sem_exec_c_p gs st2 0 st2"
    by(auto intro: sem_exec_c_p.intros)

  then show ?case using Excp_0 by blast
next
  case (Excp_Suc st1 st1' n st1'')

  obtain x l t where Cont1 : "s_cont st1 = Inl ((G x l)#t)"
    using Excp_Suc.hyps(1)
    unfolding sem_step_p_eq sem_step_def
    by(cases "s_cont st1"; auto split: list.split_asm)

  obtain st2' where St2' :  "sem_step gs st2 = Inl st2'"
    using Cont1 Excp_Suc.prems
    by(auto simp add: sem_step_def)

  hence Step2 : "sem_step_p gs st2 st2'"
    unfolding sem_step_p_eq
    by auto

  have Cont2 : "s_cont st1' = s_cont st2'"
    using sleekD2[OF H Excp_Suc.prems(2) Excp_Suc.prems(1), of x] Cont1 Excp_Suc.hyps(1) St2' 
    Excp_Suc.prems
    unfolding sem_step_p_eq
    by(auto simp add: sem_step_def)

  have Pay2 : "payload st1' = payload st2'"
    using sleekD1[OF H Excp_Suc.prems(2) Excp_Suc.prems(1), of x] Cont1 Excp_Suc.hyps(1) St2' 
    Excp_Suc.prems
    unfolding sem_step_p_eq
    by(auto simp add: sem_step_def)

  obtain st2'' where St2'' : "sem_exec_c_p gs st2' n st2''" and
    Cont2' : "payload st1'' = payload st2''" and
    Pay2' : "s_cont st1'' = s_cont st2''"
    using Excp_Suc.IH[OF Cont2 Pay2] by blast

  have Conc' : "sem_exec_c_p gs st2 (Suc n) st2''"
    using sem_exec_c_p.intros(2)[OF Step2 St2''] by auto

  then show ?case using Cont2' Pay2' by blast
qed


definition step_limit_state ::
  "('syn, 'mstate) semc \<Rightarrow> 'mstate \<Rightarrow> 'syn gensyn list \<Rightarrow> nat \<Rightarrow> bool" where
"step_limit_state gs m c n =
  (\<exists> full . s_cont full = Inl c \<and> payload full = m \<and> step_limit gs full n)"

lemma step_limit_state_unique :
  assumes H : "sleek gs"
  shows "\<exists>! n . step_limit_state gs st c n" unfolding step_limit_state_def
proof-
  obtain full :: "('a, 'b) control" where Full : "full = (mdp 0 (Some (mdt (c))), mdp 0 None, st)"
    by simp

  have Full_spec : "s_cont full = Inl c \<and> payload full = st"
    unfolding Full
    by(auto simp add: s_cont_def)

  obtain n where N: "step_limit gs full n" using step_limit_unique[of gs full] by auto

  show "\<exists>!n. \<exists>full. s_cont full = Inl c \<and> payload full = st \<and> step_limit gs full n"
  proof
    show "\<exists>full. s_cont full = Inl c \<and> payload full = st \<and> step_limit gs full n"
      using N Full_spec by blast
  next
    fix na
    assume "\<exists>full. s_cont full = Inl c \<and> payload full = st \<and> step_limit gs full na"

    then obtain full' :: "('a, 'b) control" where Full': "s_cont full' = Inl c \<and> payload full' = st \<and> step_limit gs full' na"
      by auto

    then have Full'_lim : "step_limit gs full' na" by blast

    have PayEq : "payload full = payload full'" using Full_spec Full'
      by auto

    have ContEq : "s_cont full = s_cont full'" using Full_spec Full'
      by auto

    show "na = n"
    proof(cases "(\<exists>m'. sem_exec_c_p gs full n m' \<and> s_cont m' = Inl [])")
      case True
      then obtain full2 where Full2_Exec :  "sem_exec_c_p gs full n full2" and Full2_Cont : "s_cont full2 = Inl []"
        by auto

      obtain full2' where "sem_exec_c_p gs full' n full2' \<and> s_cont full2' = Inl []"
        using sleek_exec[OF H PayEq ContEq Full2_Exec] Full2_Cont by auto

      hence Full'_lim' : "step_limit gs full' n"
        unfolding step_limit_def by blast

      show ?thesis using step_limit_unique[of gs full'] Full'_lim Full'_lim'
        by blast
    next
      case False

      have False' : "n = 0 \<and>  (\<forall>n' m'. sem_exec_c_p gs full n' m' \<longrightarrow> s_cont m' \<noteq> Inl [])"
        using False Full'_lim N unfolding step_limit_def
        by blast

      have N_zero : "n = 0" using False' by blast

      have "(\<forall>n' m'. sem_exec_c_p gs full n' m' \<longrightarrow> s_cont m' \<noteq> Inl [])"
        using False'
        by blast

      hence Noexec : "(\<And> n' m'. sem_exec_c_p gs full n' m' \<Longrightarrow> s_cont m' \<noteq> Inl [])"
        by auto
        
      show ?thesis
      proof(cases na)
        case 0
        then show ?thesis using N_zero by auto
      next
        case (Suc na')

        then have "(\<exists>m'. sem_exec_c_p gs full' na m' \<and> s_cont m' = Inl [])"
          using Full'_lim unfolding step_limit_def by blast

        then obtain full2' where "sem_exec_c_p gs full' na full2' \<and> s_cont full2' = Inl []"
          by blast

        then have Full'_exec : "sem_exec_c_p gs full' na full2'" and
          Full2'_cont : "s_cont full2' = Inl []"
          by auto

        obtain full2 where "sem_exec_c_p gs full na full2 \<and> s_cont full2 = Inl []"
          using sleek_exec[OF H sym[OF PayEq] sym[OF ContEq] Full'_exec] Full2'_cont
          by auto

        then have False using Noexec[of na full2] by auto

        thus ?thesis by auto
      qed
    qed
  qed
qed

(*step_limit gs full' na *)

definition step_limit_state_f ::
  "('syn, 'mstate) semc \<Rightarrow> 'mstate \<Rightarrow> 'syn gensyn list \<Rightarrow> nat" where
"step_limit_state_f gs m c =
  ((THE n . (\<exists> full . s_cont full = Inl c \<and> payload full = m \<and> step_limit gs full n)))"

lemma step_limit_state_f_step_limit :
  assumes H : "sleek gs"
  shows "step_limit_state gs m l (step_limit_state_f gs m l)"
  using theI'[OF step_limit_state_unique[OF H, of m l]]
  unfolding step_limit_state_def step_limit_state_f_def
  by auto


lemma HWhileC:
  assumes H0 : "gs = \<lparr> s_sem = pcomps' fs \<rparr>"
  (*assumes H1 : "seq_sem_l_gen lfts \<in> set fs" *)
  assumes HF : "f = imp_sem_l_gen lfts"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hnemp : "g \<in> set fs"
  assumes Hdom : "(f \<downharpoonleft> (set fs) SwhileC')"
  assumes Hsyn : "lfts Swhile' = SwhileC"
  assumes Hsleek : "sleek gs"
  (* TODO: generalize. these should be expressed using valid-sets *)
  assumes P1_valid : "\<And> st.  P1 st \<Longrightarrow> get_cond st \<noteq> None"
  (* is this correct? *)
  assumes Htrue : "|gs| {-(\<lambda> _ _ . True)-} {=(\<lambda> st g . P1 st) =} [body] {=(\<lambda> st g . P1 st) =}"
  shows "|gs| {- (\<lambda> (_ :: nat) _ . True) -} {= (\<lambda> st g . P1 st)  =} [G SwhileC' [body]] {= (\<lambda> st g . P1 st \<and> get_cond st = Some False) =}"
proof
  fix c' 
  fix g g' :: nat

  assume True
  term "gs"
  assume Cnc : "|gs| {\<lambda>st. C (P1 st \<and> get_cond st = Some False)} g' c'"

  obtain PX where PX_def : "PX = (\<lambda> (n :: nat) st . (P1 st \<and> 
    (\<forall> c st' . n = 0 \<longrightarrow> payload st' = st \<longrightarrow> s_cont st' = Inl ([G SwhileC' [body]] @ c) \<longrightarrow> safe gs st')))"
    by simp

  have PX_cond : "(\<And>n st. PX n st \<Longrightarrow> get_cond st \<noteq> None)"
    unfolding PX_def
    using P1_valid
    by blast

  have BodySpec : "|gs| {-\<lambda>g g'. g' = g - 1-} {=\<lambda>st g. step_limit_state_f gs st [body] st \<le> g \<and> PX g st=} [body] {=\<lambda>st g. getn st \<le> g \<and> PX g st=}"


  have PX_imp : "(\<And>n st. PX n st \<Longrightarrow> P1 st)"
    unfolding PX_def by auto
(*
  have "(\<And>st. P1 (payload st) \<Longrightarrow> PX (step_limit_f gs st) (payload st))"
*)

  have Gen : "|gs| {-\<lambda>g g'.
            g' = g-} {=\<lambda>st g. step_limit_state_f gs st [G SwhileC' [body]]  \<ge> g \<and> PX g st=} [G SwhileC' [body]] {=\<lambda>st g. (\<exists>n\<le>g. PX n st \<and> get_cond st = Some False)=}"
  proof
    fix c' 
    fix g g' :: nat
    assume Geq : "g' = g"
    assume Gd : "|gs| {\<lambda>st g. \<exists>n\<le>g. PX n st \<and> get_cond st = Some False} g' c'"
    show "|gs| {\<lambda>st g. step_limit_state_f gs st [G SwhileC' [body]] \<ge> g \<and> PX g st} g
        ([G SwhileC' [body]] @ c')"
    proof
      fix mw :: "('a, 'b) state"

      assume Lim_PXw : "step_limit_state_f gs (payload mw) [G SwhileC' [body]] \<ge> g \<and> PX g (payload mw)"

      obtain lim' where Lim'_def : "lim' = step_limit_state_f gs (payload mw) [G SwhileC' [body]]"
        by simp

      have Lim : "step_limit_state_f gs (payload mw) [G SwhileC' [body]] \<ge> g"
        and PXw : "PX g (payload mw)"
        using Lim_PXw
        by auto

      assume Contw : "s_cont mw = Inl ([G SwhileC' [body]] @ c')"

      show "safe gs mw"

      proof(cases g)
        case 0

        have PXw_alt : "(\<And> c st'.
            g = 0 \<Longrightarrow>
            payload st' = payload mw \<Longrightarrow>
            s_cont st' =
            Inl ([G SwhileC' [body]] @ c) \<Longrightarrow>
            safe gs st')"
          using PXw unfolding PX_def
          by blast

        show ?thesis using PXw_alt[OF 0 refl Contw] by blast
      next
        case (Suc nat)

        have Limit_st : "step_limit_state gs (payload mw) [G SwhileC' [body]] (lim')"
          unfolding Lim'_def
          using step_limit_state_f_step_limit[OF Hsleek] by blast

        obtain full where Full_cont : "s_cont full = Inl [G SwhileC' [body]]" and
          Full_pay : "payload full = payload mw" and 
          Full_lim : "step_limit gs full (lim')"
          using Limit_st
          unfolding step_limit_state_def
          by blast

        have Conc' : "safe gs full" using step_limit_safe[OF Full_lim]
          using Lim Suc
          unfolding Lim'_def
          by auto

        have Full_cont_eq : "s_cont full = s_cont mw" using Full_cont Contw
          by auto

        show ?thesis
        proof
          fix mw' :: "('a, 'b) state"

          assume Execw' : "sem_exec_p gs mw mw'"

          obtain nw where Execw'_c : "sem_exec_c_p gs mw nw mw'"
            using exec_p_imp_exec_c_p[OF Execw'] by blast

          show "imm_safe gs mw'" using guardedD[OF Gd]
            using sleek_exec[OF Hsleek Full_pay]
            sorry
        qed
      qed
    qed
  qed
      (* um... do we even need the general theorem for this? *)
  have Rest : "\<And> ga . |gs| {\<lambda>st g. \<exists>n\<le>g. PX n st \<and> get_cond st = Some False} ga c'"
  proof
    fix ga :: nat
    fix mz :: "('a, 'b) state"
    assume H1 : "\<exists>n\<le>ga . PX n (payload mz) \<and> get_cond (payload mz) = Some False"
    assume H2 : "s_cont mz = Inl c'"

    obtain n where N: "PX n (payload mz) \<and> get_cond (payload mz) = Some False"
      using H1 by auto

    hence N' : "P1 (payload mz) \<and> get_cond (payload mz) = Some False"
      using PX_imp[of n "payload mz"] by auto

    show "safe gs mz"
      using guardedD[OF Cnc N' H2] by auto
  qed

  have Newguard : "\<And> ga . |gs| {\<lambda>st g. step_limit_state_f gs st [G SwhileC' [body]] \<ge> g \<and> PX g st} ga ([G SwhileC' [body]] @ c')"
  proof-
    fix ga
    show "|gs| {\<lambda>st g. step_limit_state_f gs st [G SwhileC' [body]] \<ge> g \<and> PX g st} ga ([G SwhileC' [body]] @ c')"
    using HTE[OF Gen refl Rest[of ga]] 
    by auto
  qed

  show "|gs| {\<lambda>st. C (P1 st)} g ([G SwhileC' [body]] @ c')"
    using HWhileC_gen[OF H0 HF Hpres Hnemp Hdom Hsyn]
(*
  proof
    fix mz :: "('a, 'b) state"
    assume H1 : "P1 (payload mz)" 
    assume H2 :  "s_cont mz = Inl ([G SwhileC' [body]] @ c')"


    have PX_fact : "PX (step_limit_state_f gs (payload mz) [G SwhileC' [body]]) (payload mz)" 
      unfolding PX_def
      sorry (* true but slightly annoying *)

    show "safe gs mz"
      using guardedD[OF Newguard, of "step_limit_state_f gs (payload mz) [G SwhileC' [body]]", OF _ H2] PX_fact

      by auto
  qed
*)
qed


end