theory Hoare_Step imports Hoare Hoare_Indexed Hoare_Direct
 "../Lifter/Auto_Lifter_Proofs"
 "../Mergeable/Mergeable_Instances"
 "../Composition/Composition" "../Composition/Dominant"
 "../Language_Components/Seq/Seq_Hoare"
 "Hoare_Lift" "Hoare_Lift_Transform"
begin

(* 
 * When dealing with single-step languages, we have an important special case - that is,
 * the case where the single-step language is _dominant_ (see Composition/Dominant.thy)
 * for one or more pieces of syntax. In such cases we can show that the
 * lifted version of the rule holds without side conditions.
 *)

(* However, we might be able to avoid reasoning about liftings at all in such cases (?)
 * by playing the same parametricity trick as with the control languages?
 *)

(* turn an f on payloads into an f on control that ignores the control contents.
 * this can probably be a lifting actually *)
(*
definition no_control_lifting :: "('a, 'b :: {Bogus, Pord}, ('x, 'b) control) lifting" where
"no_control_lifting =
  schem_lift NC (SP NX (SP NX (SID NC)))"
*)
definition no_control_lifting :: "('a, 'b1, 'b2 :: {Bogus, Pord}) lifting \<Rightarrow>
  ('a, 'b1 , ('x, 'b2) control) lifting" where
"no_control_lifting l =
  schem_lift NC (SP NX (SP NX (SINJ l NC)))"

lemma zztest :
  obtains ntest :: nat where True
  by auto


(* something is weird with the pord constraint here. *)
definition no_control_l :: "
('a, 'b1, 'b2 :: {Bogus, Pord}) lifting \<Rightarrow>
('a \<Rightarrow> 'b1 \<Rightarrow> 'b1 :: {Bogus, Pord}) \<Rightarrow>
('a \<Rightarrow> ('x, 'b2 :: {Bogus, Pord}) control \<Rightarrow> ('x, 'b2 ) control)" where
"no_control_l l f =
  lift_map_s id (no_control_lifting l) f"
  

(* TODO: this hypothesis is rather inconvenient. *)
(* TODO: there is a not-very-nice control flow interaction here, wherein we actually
 * need to remove the head...
 * seq handles this, but we need to figure out how to express that this will be handled
 * by another semantics - something like a generalization of dominates?
 *)
(* so, if we merge with sequence, we are most of the way there.
 * however, we need to show that sequence doesn't get overridden
 * by other control semantics.
   * idea: we can actually use dominance here.
   * all we need to do is say that seq is dominant for that syntax
   * for all _other_ semantics. no_control_lifting should do the rest. i think.
 *)

(* can we get away with lift_pred_s? looks like the answer is no; see below. *)

(* YOU ARE HERE.
   The main thing i am trying to figure out now is how big of an issue this is.
   on the one hand it means that these rules might not naturally compose between
   different liftings (which will have different valid sets).

   A weaker, alternate notion of lifting validity (updates are only guaranteed to be in
   the valid set if we started in the valid set) feels very ugly, but i worry i am running
   out of other options.
*)

lemma HTS_imp_HT' :
  assumes H: "f % {{P1}} c {{P2}}"
  assumes Valid : "lifting_validx l S"
  assumes Hf' : "f' = no_control_l l f"
  assumes H0 : "gs = pcomps fs"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hseq : "seq_sem_l_gen lfts \<in> set fs"
  assumes Skip : "lfts c = Sskip"
  assumes Hnemp : "g \<in> (set fs - {seq_sem_l_gen lfts})"
  assumes Hdom : "(f' \<downharpoonleft> (set fs - {seq_sem_l_gen lfts}) c)"
  shows "|gs| {~ (lift_pred_validx_s id l c P1) ~} [G c z] {~ (lift_pred_validx_s id l c P2) ~}"
proof(rule HT'I)
  fix npost

  have Valid' : "lifting_valid l S"
    using lifting_validxDV[OF Valid] by auto

  have "|#gs#| {#-lift_pred_validx_s id l c
                     P1, (0 +
                          npost)-#} [G c z] {#-lift_pred_validx_s id l c
       P2, npost-#}"
    unfolding add_0
  proof
    fix c'

    assume Guard : "|#gs#| {#lift_pred_validx_s id l c P2, npost#} c'"
    show "|#gs#| {#lift_pred_validx_s id l c P1, npost#} ([G c z] @ c')"
    proof
      fix m :: "('a, 'c) control"
      assume Hpay : "lift_pred_validx_s id l c P1 (payload m)"
      assume Hcont : "cont m = Inl ([G c z] @ c') "

      have Hpay1 : "P1 (LOut l c (payload m))" and Hpay2 : "payload m \<in> S c" and Hpay3 : "payload m \<in> ok_S"
        using Hpay lifting_validxDS[OF Valid]
        unfolding lift_pred_valid_s_def lift_pred_validx_s_def lift_pred_s_def
        by auto

      have Hpay' : "P2 (f c (LOut l c (payload m)))"
        using HTSE[OF H Hpay1]
        by simp

      show "safe_for gs m npost"
      proof(cases "(sem_step gs m)")
        case (Inr bad)
  
        then have False using Hcont H0
          by(auto simp add: sem_step_def)
  
        then show ?thesis by auto
      next
        case (Inl m')

        have Pres' : "sups_pres (set fs - {seq_sem_l_gen lfts})"
          using sups_pres_subset[OF Hpres, of "set fs - {seq_sem_l_gen lfts}"] by auto

        obtain fs_sub where Fs_sub : "set fs_sub = set fs - {seq_sem_l_gen lfts}"
          using finite_list[of "set fs - {seq_sem_l_gen lfts}"]
          by auto

(* ok, so the idea now is:
- we know full step (op + control flow) leads to m'
- dominance over everything but the seq means we can treat it as
  "op (dominant thing) then seq"
- we can then unfold these things in order and everything should be ok.
*)

        have Assoc : 
             "pcomps (fs_sub @ [seq_sem_l_gen lfts]) =
              pcomps [pcomps fs_sub, pcomps [seq_sem_l_gen lfts]]"
        proof(rule pcomps_assoc)

          have "set fs - {seq_sem_l_gen lfts} \<union> set [seq_sem_l_gen lfts] = set fs"
            using Hseq 
            by(simp; blast)

          then show "sups_pres (set fs_sub \<union> set [seq_sem_l_gen lfts])"
            unfolding Fs_sub
            using Hpres
            by auto
        next

          have "set fs_sub \<noteq> {}" using Hnemp unfolding Fs_sub by auto

          then show "fs_sub \<noteq> []" by auto
        next

          show "[seq_sem_l_gen lfts] \<noteq> []" by simp
        qed

        have Set_alt : "set (fs_sub @ [seq_sem_l_gen lfts]) = set fs"
          unfolding set_append Fs_sub
          using Un_Diff_cancel2 Hseq
          by auto

        have Gs_alt : "gs = pcomps (fs_sub @ [seq_sem_l_gen lfts])"
          using pcomps_set_eq[OF Hpres Hseq _ Set_alt, of fs] H0
          by auto
          
(* TODO: find a better solution than this awful type annotation hack *)
        have Seq_pres : 
          "sups_pres {(seq_sem_l_gen lfts  :: ('a \<Rightarrow> 'a gensyn list md_triv option md_prio \<times>
            String.literal md_triv option md_prio \<times> 'c
            \<Rightarrow> 'a gensyn list md_triv option md_prio \<times>
               String.literal md_triv option md_prio \<times>
               'c))}"
          using sups_pres_subset[OF Hpres, of "{seq_sem_l_gen lfts}"] Hseq
          by(auto)


        have Gs_alt' : "gs = pcomps [pcomps fs_sub, seq_sem_l_gen lfts]"
          using Gs_alt pcomps_singleton[OF Seq_pres, of "[seq_sem_l_gen lfts]"]
          unfolding Assoc
          unfolding append.simps H0
          by auto

        have Hdom' :  "f' \<downharpoonleft> (set fs_sub) c"
          using Fs_sub Hdom by auto
        have Dominate1 : "pcomps fs_sub c m = f' c m" using dominant_pcomps[OF _ _ Hdom', of g m] Pres' Hnemp Fs_sub
          by auto

(* almost have this. the missing ingredient is using the fact that
 * information content will increase (for a strong-valid lifting) *)

(* TODO: declare a lemmas with all the definitions of liftings... *)
        obtain pri1 pri2 rest where Msplit :
          "m = (mdp pri1 (Some (mdt (G c z # c'))), mdp pri2 None, rest)"
          and Rest : "rest \<in> ok_S"
          using Gs_alt' Dominate1 Skip Hpay Hcont Hf'
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def 
            lift_pred_valid_s_def lift_pred_validx_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)

        have Rest' : "rest \<in> S c"
          using lifting_validxDS[OF Valid] Rest by auto

        have LUpd_rest1 :
          "rest <[ LUpd l c (f c (LOut l c rest)) rest"
          using lifting_validDI[OF Valid' Rest']
          by auto

        have LUpd_rest2 : "[^ LUpd l c (f c (LOut l c rest)) rest, rest ^] = LUpd l c (f c (LOut l c rest)) rest"
          using bsup_base_leq2[OF LUpd_rest1]
          by simp

        then have LOut_m : "LOut (no_control_lifting l) c (gs c m) = LOut (no_control_lifting l) c (f' c m)"
          using Gs_alt' Dominate1 Skip Hpay Hcont Hf' Msplit
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def 
            lift_pred_valid_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)


(* key sub-result. *)
        have Pay_final : "payload m' = LUpd l c (f c (LOut l c (payload m))) (payload m)"
          using Gs_alt' Dominate1 Skip Hpay Hcont Hf' Msplit Inl LUpd_rest2
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            lift_pred_valid_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)

(* key sub-result. idea here is that no_control_l means we won't overwrite. *)
        have Cont_final : "cont m' = cont (seq_sem_l_gen lfts c m)"
          using Hcont Msplit Skip Inl Gs_alt' Dominate1 Hf'
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            lift_pred_valid_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def prio_bsup option_bsup leq_refl
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)         

        hence Cont_final' : "cont m' = Inl c'"
          using Hcont Msplit Skip
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            lift_pred_valid_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)

        have Conc' : "safe_for gs m' npost"
          using guardediD[OF Guard, of "m'"] Hpay' Cont_final'
          unfolding Pay_final Cont_final' lift_pred_valid_s_def lift_pred_s_def lift_pred_validx_s_def
          using lifting_validDO[OF Valid'] lifting_validDP[OF Valid'] lifting_validxDP'[OF Valid Hpay3]
          by(cases m; auto)

        have Inl_alt : "sem_step_p gs m m'"
          using Inl unfolding sem_step_p_eq by simp

        show  "safe_for gs m npost"
          using safe_for_weaken[OF safe_for_extend[OF Conc' Excp_1[OF Inl_alt]], of npost]
          by simp
      qed
    qed
  qed

  thus "\<exists>npre.
          |#gs#| {#-lift_pred_validx_s id l c
                     P1, (npre + npost)-#} [G c z] {#-lift_pred_validx_s id l c P2, npost-#}"
    by blast
qed


lemma HTS_imp_HT'' :
  fixes f :: "'syn0 \<Rightarrow> 'st0 \<Rightarrow> 'st0"
  fixes x :: "'syn1"
  fixes l' :: "('syn1 \<Rightarrow> 'syn0)"
  assumes H: "f % {{P'}} (l' x) {{Q'}}"
  assumes Valid : "lifting_validx l S"
  assumes Hf' : "f' = lift_map_s l' (no_control_lifting  l) f"
  assumes H0 : "gs = pcomps fs"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hseq : "seq_sem_l_gen lfts \<in> set fs"
  assumes Skip : "lfts x = Sskip"
  assumes Hnemp : "g \<in> (set fs - {seq_sem_l_gen lfts})"
  assumes Hdom : "(f' \<downharpoonleft> (set fs - {seq_sem_l_gen lfts}) x)"
  assumes P1_ok : "\<And> st . P st \<Longrightarrow> st \<in> ok_S"
  assumes HP : "\<And> st . P st \<Longrightarrow> P' (LOut l (l' x) st)"

  shows "|gs| {~ (\<lambda> st . P st) ~} [G x z] 
    {~ (\<lambda> st . \<exists> old_big small_new . P old_big \<and> Q' small_new \<and> st = LUpd l (l' x) small_new old_big) ~}"
  (*shows "\<And> P1 . |gs| {~ P1 ~} [G c z] {~ (liftt_conc id l c P2 P1) ~}"*)
proof(rule HT'I)
  term "l'"
  term "gs"
  fix npost
  have Valid' : "lifting_valid l S"
    using lifting_validxDV[OF Valid] by auto

  have "|#gs#| {#-(\<lambda>st. P st), (0 + npost)-#} [G x z] {#-(\<lambda>st. \<exists>old_big small_new.
            P old_big \<and>
            Q' small_new \<and>
            st = LUpd l (l' x)  small_new old_big), npost-#}"
    unfolding add_0
  proof
    fix c'

    assume Guard : " |#gs#| {#(\<lambda>st. \<exists>old_big small_new.
                            P old_big \<and>
                            Q' small_new \<and>
                            st =
                            LUpd l (l' x) small_new
                             old_big), npost#} c'"
    show "|#gs#| {#P, npost#} ([G x z] @ c')"
    proof
      fix m 
      assume Hpay0 : "P (payload m)" and Hcont : "cont m = Inl ([G x z] @ c') "

      show "safe_for gs m npost"
      proof(cases "(sem_step gs m)")
        case (Inr bad)
  
        then have False using Hcont H0
          by(auto simp add: sem_step_def)
  
        then show ?thesis by auto
      next
        case (Inl m')

        have Pres' : "sups_pres (set fs - {seq_sem_l_gen lfts})"
          using sups_pres_subset[OF Hpres, of "set fs - {seq_sem_l_gen lfts}"] by auto

        obtain fs_sub where Fs_sub : "set fs_sub = set fs - {seq_sem_l_gen lfts}"
          using finite_list[of "set fs - {seq_sem_l_gen lfts}"]
          by auto

(* ok, so the idea now is:
- we know full step (op + control flow) leads to m'
- dominance over everything but the seq means we can treat it as
  "op (dominant thing) then seq"
- we can then unfold these things in order and everything should be ok.
*)

        have Assoc : 
             "pcomps (fs_sub @ [seq_sem_l_gen lfts]) =
              pcomps [pcomps fs_sub, pcomps [seq_sem_l_gen lfts]]"
        proof(rule pcomps_assoc)

          have "set fs - {seq_sem_l_gen lfts} \<union> set [seq_sem_l_gen lfts] = set fs"
            using Hseq 
            by(simp; blast)

          then show "sups_pres (set fs_sub \<union> set [seq_sem_l_gen lfts])"
            unfolding Fs_sub
            using Hpres
            by auto
        next

          have "set fs_sub \<noteq> {}" using Hnemp unfolding Fs_sub by auto

          then show "fs_sub \<noteq> []" by auto
        next

          show "[seq_sem_l_gen lfts] \<noteq> []" by simp
        qed

        have Set_alt : "set (fs_sub @ [seq_sem_l_gen lfts]) = set fs"
          unfolding set_append Fs_sub
          using Un_Diff_cancel2 Hseq
          by auto

        have Gs_alt : "gs = pcomps (fs_sub @ [seq_sem_l_gen lfts])"
          using pcomps_set_eq[OF Hpres Hseq _ Set_alt, of fs] H0
          by auto


        have Hpay : "P (payload m)"
          using Hpay0
          by auto

        then have Hpay_S : "payload m \<in> ok_S"
          using P1_ok[of "payload m"] by auto

        have Hpay1' : "LOut l (l' x) (payload m) = LOut l (l' x) (payload m) \<and> P (payload m)"
          using Hpay
          by simp

      have Hpay' : "Q' (f (l' x) (LOut l (l' x) (payload m)))"
        using HTSE[OF H ] HP[OF Hpay]
        by auto

  (*
        then have Hpay1 : "\<exists>full. LOut l (id c) full = LOut l c (payload m) \<and> P1 full" using Hpay_S
          by auto

        have Hpay' : " P2 (\<lambda>st. \<exists>full. LOut l (id c) full = st \<and> P1 full) (f c (LOut l c (payload m)))"
          using HTSE[OF H ] Hpay1
          by auto
*)
(* TODO: find a better solution than this awful type annotation hack *)

        have Seq_pres : 
          "sups_pres {(seq_sem_l_gen lfts  ::('syn1 \<Rightarrow> 'syn1 gensyn list md_triv option md_prio \<times>
            String.literal md_triv option md_prio \<times> 'a
            \<Rightarrow> 'syn1 gensyn list md_triv option md_prio \<times>
               String.literal md_triv option md_prio \<times>
               'a))}"
          using sups_pres_subset[OF Hpres, of "{(seq_sem_l_gen lfts )}"] Hseq
          by(auto)

        have Gs_alt' : "gs = pcomps [pcomps fs_sub, seq_sem_l_gen lfts]"
          using Gs_alt pcomps_singleton[OF Seq_pres, of "[seq_sem_l_gen lfts]"]
          unfolding Assoc
          unfolding append.simps H0
          by auto

        have Hdom' :  "f' \<downharpoonleft> (set fs_sub) x"
          using Fs_sub Hdom by auto

        have Dominate1 : "pcomps fs_sub x m = f' x m" using dominant_pcomps[OF _ _ Hdom', of g m] Pres' Hnemp Fs_sub
          by auto

(* YOU ARE HERE. *)
(* problem: seems like we still need to know something about the validity of the initial state.
   maybe this is OK, but i worry that it will create problems.
   the obvious solution is just to throw the validity condition into the pre and post conditions.
   but let's think about whether that will have unintended consequences.
 *)
        obtain pri1 pri2 rest where Msplit :
          "m = (mdp pri1 (Some (mdt (G x z # c'))), mdp pri2 None, rest)" and Rest : "rest \<in> ok_S"
          using Gs_alt' Dominate1 Skip Hpay Hcont Hf' Hpay_S
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def 
            lift_pred_valid_s_def lift_pred_validx_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)

        have Rest' : "rest \<in> S (l' x)"
          using lifting_validxDS[OF Valid] Rest by auto

        have LUpd_rest1 :
          "rest <[ LUpd l (l' x) (f (l' x) (LOut l (l' x) rest)) rest"
          using lifting_validDI[OF Valid' Rest']
          by auto

        have LUpd_rest2 : "[^ LUpd l (l' x) (f (l' x) (LOut l (l' x) rest)) rest, rest ^] = LUpd l (l' x) (f (l' x) (LOut l (l' x) rest)) rest"
          using bsup_base_leq2[OF LUpd_rest1]
          by simp

        then have LOut_m : 
          "LOut (l_synt l' (no_control_lifting l)) x (gs x m) = LOut (l_synt l' (no_control_lifting l)) x (f' x m)"
          using Gs_alt' Dominate1 Skip Hpay Hcont Hf' Msplit
          unfolding l_synt_def
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def 
            lift_pred_valid_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)


(* key sub-result. *)

(* key sub-result. idea here is that no_control_l means we won't overwrite. *)
        have Cont_final : "cont m' = cont (seq_sem_l_gen lfts x m)"
          using Hcont Msplit Skip Inl Gs_alt' Dominate1 Hf'
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            lift_pred_valid_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def prio_bsup option_bsup leq_refl
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)         

        hence Cont_final' : "cont m' = Inl c'"
          using Hcont Msplit Skip
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            lift_pred_valid_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)

        have Pay_final : "payload m' = LUpd l (l' x) (f (l' x) (LOut l (l' x) (payload m))) (payload m)"
          using Gs_alt' Dominate1 Skip Hpay Hcont Hf' Msplit Inl LUpd_rest2
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            lift_pred_valid_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)

(* YOU ARE HERE *)
(* TODO: we need to pull out the "ok_S" piece. *)
        have "(P (payload m)) \<and> Q' ((f (l' x) (LOut l (l' x) (payload m)))) \<and>
              payload m' = LUpd l (l' x) (f (l' x) (LOut l (l' x) (payload m)))(payload m)"
          using Hpay' Pay_final Hpay_S Hpay
          by(auto)

        then have Guard_Hyp : "\<exists>old_big small_new.
             P old_big \<and>
             Q' small_new \<and>
             payload m' = LUpd l (l' x) small_new old_big"
          by auto

        have Conc' : "safe_for gs m' npost"
          using guardediD[OF Guard, of "m'"]  Cont_final' Guard_Hyp 
          unfolding Pay_final Cont_final' lift_pred_valid_s_def lift_pred_s_def lift_pred_validx_s_def
            liftt_conc_def
          using lifting_validDO[OF Valid'] lifting_validDP[OF Valid'] lifting_validxDP'[OF Valid ]
          by(cases m; auto)

        have Inl_alt : "sem_step_p gs m m'"
          using Inl unfolding sem_step_p_eq by simp

        show  "safe_for gs m npost"
          using safe_for_weaken[OF safe_for_extend[OF Conc' Excp_1[OF Inl_alt]], of npost]
          by simp
      qed
    qed
  qed

  thus "\<exists>npre.
          |#gs#| {#-P, (npre +
                        npost)-#} [G x
  z] {#-(\<lambda>st. \<exists>old_big small_new.
                  P old_big \<and>
                  Q' small_new \<and>
                  st = LUpd l (l' x) small_new old_big), npost-#}"
    by blast
qed

lemma HTS_imp_HT''old :
  assumes H: "\<And> P1 . f % {{P1}} c {{P2 P1}}"
  assumes Valid : "lifting_validx l S"
  assumes Hf' : "f' = no_control_l l f"
  assumes H0 : "gs = pcomps fs"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hseq : "seq_sem_l_gen lfts \<in> set fs"
  assumes Skip : "lfts c = Sskip"
  assumes Hnemp : "g \<in> (set fs - {seq_sem_l_gen lfts})"
  assumes Hdom : "(f' \<downharpoonleft> (set fs - {seq_sem_l_gen lfts}) c)"
  assumes P1_ok : "\<And> st . P1 st \<Longrightarrow> st \<in> ok_S"
  shows "|gs| {~ (\<lambda> st . P1 st) ~} [G c z] {~ (\<lambda> st . liftt_conc id l c P2 P1 st) ~}"
  (*shows "\<And> P1 . |gs| {~ P1 ~} [G c z] {~ (liftt_conc id l c P2 P1) ~}"*)
proof(rule HT'I)
  fix npost

  have Valid' : "lifting_valid l S"
    using lifting_validxDV[OF Valid] by auto

  have "|#gs#| {#-(\<lambda>st. P1 st), (0 +
            npost)-#} [G c z] {#-(\<lambda>st.
        liftt_conc id l c P2 P1 st), npost-#}"
    unfolding add_0
  proof
    fix c'

    assume Guard : "|#gs#| {#(\<lambda>st. liftt_conc id l c P2 P1 st ), npost#} c'"
    show "|#gs#| {#(\<lambda>st. P1 st), npost#} ([G c z] @ c')"
    proof
      fix m 
      assume Hpay0 : "P1 (payload m)" and Hcont : "cont m = Inl ([G c z] @ c') "

      show "safe_for gs m npost"
      proof(cases "(sem_step gs m)")
        case (Inr bad)
  
        then have False using Hcont H0
          by(auto simp add: sem_step_def)
  
        then show ?thesis by auto
      next
        case (Inl m')

        have Pres' : "sups_pres (set fs - {seq_sem_l_gen lfts})"
          using sups_pres_subset[OF Hpres, of "set fs - {seq_sem_l_gen lfts}"] by auto

        obtain fs_sub where Fs_sub : "set fs_sub = set fs - {seq_sem_l_gen lfts}"
          using finite_list[of "set fs - {seq_sem_l_gen lfts}"]
          by auto

(* ok, so the idea now is:
- we know full step (op + control flow) leads to m'
- dominance over everything but the seq means we can treat it as
  "op (dominant thing) then seq"
- we can then unfold these things in order and everything should be ok.
*)

        have Assoc : 
             "pcomps (fs_sub @ [seq_sem_l_gen lfts]) =
              pcomps [pcomps fs_sub, pcomps [seq_sem_l_gen lfts]]"
        proof(rule pcomps_assoc)

          have "set fs - {seq_sem_l_gen lfts} \<union> set [seq_sem_l_gen lfts] = set fs"
            using Hseq 
            by(simp; blast)

          then show "sups_pres (set fs_sub \<union> set [seq_sem_l_gen lfts])"
            unfolding Fs_sub
            using Hpres
            by auto
        next

          have "set fs_sub \<noteq> {}" using Hnemp unfolding Fs_sub by auto

          then show "fs_sub \<noteq> []" by auto
        next

          show "[seq_sem_l_gen lfts] \<noteq> []" by simp
        qed

        have Set_alt : "set (fs_sub @ [seq_sem_l_gen lfts]) = set fs"
          unfolding set_append Fs_sub
          using Un_Diff_cancel2 Hseq
          by auto

        have Gs_alt : "gs = pcomps (fs_sub @ [seq_sem_l_gen lfts])"
          using pcomps_set_eq[OF Hpres Hseq _ Set_alt, of fs] H0
          by auto

(* not sure if we need this (ConcX) *)
(*
      have ConcX : "liftt_conc id l c P2 P1 (payload m')"
        sorry
*)
(*
      have (*Hpay1 : "P1 (LOut l c (payload m))" and *) Hpay2 : "payload m \<in> S c" and Hpay3 : "payload m \<in> ok_S"
        using Hpay lifting_validxDS[OF Valid]
        unfolding lift_pred_valid_s_def lift_pred_validx_s_def lift_pred_s_def
        by auto
*)

(*
        have Hpay2 : "payload m \<in> S c" and Hpay3 : "payload m \<in> ok_S"
        using Hpay lifting_validxDS[OF Valid]
        unfolding lift_pred_valid_s_def lift_pred_validx_s_def lift_pred_s_def
        by auto
*)

        have Hpay : "P1 (payload m)"
          using Hpay0
          by auto

        then have Hpay_S : "payload m \<in> ok_S"
          using P1_ok[of "payload m"] by auto

        have Hpay1' : "LOut l (id c) (payload m) = LOut l c (payload m) \<and> P1 (payload m)"
          using Hpay
          by simp
  
        then have Hpay1 : "\<exists>full. LOut l (id c) full = LOut l c (payload m) \<and> P1 full" using Hpay_S
          by auto

        have Hpay' : " P2 (\<lambda>st. \<exists>full. LOut l (id c) full = st \<and> P1 full) (f c (LOut l c (payload m)))"
          using HTSE[OF H ] Hpay1
          by auto

(* TODO: find a better solution than this awful type annotation hack *)
        have Seq_pres : 
          "sups_pres {(seq_sem_l_gen lfts  :: ('b \<Rightarrow> 'b gensyn list md_triv option md_prio \<times>
            String.literal md_triv option md_prio \<times> 'c
            \<Rightarrow> 'b gensyn list md_triv option md_prio \<times>
               String.literal md_triv option md_prio \<times>
               'c))}"
          using sups_pres_subset[OF Hpres, of "{seq_sem_l_gen lfts}"] Hseq
          by(auto)


        have Gs_alt' : "gs = pcomps [pcomps fs_sub, seq_sem_l_gen lfts]"
          using Gs_alt pcomps_singleton[OF Seq_pres, of "[seq_sem_l_gen lfts]"]
          unfolding Assoc
          unfolding append.simps H0
          by auto

        have Hdom' :  "f' \<downharpoonleft> (set fs_sub) c"
          using Fs_sub Hdom by auto

        have Dominate1 : "pcomps fs_sub c m = f' c m" using dominant_pcomps[OF _ _ Hdom', of g m] Pres' Hnemp Fs_sub
          by auto

(* YOU ARE HERE. *)
(* problem: seems like we still need to know something about the validity of the initial state.
   maybe this is OK, but i worry that it will create problems.
   the obvious solution is just to throw the validity condition into the pre and post conditions.
   but let's think about whether that will have unintended consequences.
 *)
        obtain pri1 pri2 rest where Msplit :
          "m = (mdp pri1 (Some (mdt (G c z # c'))), mdp pri2 None, rest)" and Rest : "rest \<in> ok_S"
          using Gs_alt' Dominate1 Skip Hpay Hcont Hf' Hpay_S
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def 
            lift_pred_valid_s_def lift_pred_validx_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)

        have Rest' : "rest \<in> S c"
          using lifting_validxDS[OF Valid] Rest by auto

        have LUpd_rest1 :
          "rest <[ LUpd l c (f c (LOut l c rest)) rest"
          using lifting_validDI[OF Valid' Rest']
          by auto

        have LUpd_rest2 : "[^ LUpd l c (f c (LOut l c rest)) rest, rest ^] = LUpd l c (f c (LOut l c rest)) rest"
          using bsup_base_leq2[OF LUpd_rest1]
          by simp

        then have LOut_m : "LOut (no_control_lifting l) c (gs c m) = LOut (no_control_lifting l) c (f' c m)"
          using Gs_alt' Dominate1 Skip Hpay Hcont Hf' Msplit
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def 
            lift_pred_valid_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)


(* key sub-result. *)

(* key sub-result. idea here is that no_control_l means we won't overwrite. *)
        have Cont_final : "cont m' = cont (seq_sem_l_gen lfts c m)"
          using Hcont Msplit Skip Inl Gs_alt' Dominate1 Hf'
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            lift_pred_valid_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def prio_bsup option_bsup leq_refl
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)         

        hence Cont_final' : "cont m' = Inl c'"
          using Hcont Msplit Skip
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            lift_pred_valid_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)

        have Pay_final : "payload m' = LUpd l c (f c (LOut l c (payload m))) (payload m)"
          using Gs_alt' Dominate1 Skip Hpay Hcont Hf' Msplit Inl LUpd_rest2
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            lift_pred_valid_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)

(* YOU ARE HERE *)
(* TODO: we need to pull out the "ok_S" piece. *)
        have "payload m' = LUpd l (id c) (f c (LOut l c (payload m)))(payload m) \<and>
               (P1 (payload m)) \<and>
               P2 (\<lambda>st. \<exists>full. LOut l (id c) full = st \<and> (P1 full)) (f c (LOut l c (payload m)))"
          using Hpay' Pay_final Hpay_S Hpay
          by(auto)

        then have Guard_Hyp : "\<exists>old st_small.
           payload m' = LUpd l (id c) st_small old \<and>
           (P1 old) \<and>
           P2 (\<lambda>st. \<exists>full. LOut l (id c) full = st \<and>
                            P1 full)
            st_small"
          by blast

        have Conc' : "safe_for gs m' npost"
          using guardediD[OF Guard, of "m'"] Hpay' Cont_final' Guard_Hyp 
          unfolding Pay_final Cont_final' lift_pred_valid_s_def lift_pred_s_def lift_pred_validx_s_def
            liftt_conc_def
          using lifting_validDO[OF Valid'] lifting_validDP[OF Valid'] lifting_validxDP'[OF Valid ]
          by(cases m; auto)

        have Inl_alt : "sem_step_p gs m m'"
          using Inl unfolding sem_step_p_eq by simp

        show  "safe_for gs m npost"
          using safe_for_weaken[OF safe_for_extend[OF Conc' Excp_1[OF Inl_alt]], of npost]
          by simp
      qed
    qed
  qed

  thus " \<exists>npre.
          |#gs#| {#-P1, (npre +
                         npost)-#} [G c
              z] {#-liftt_conc id l c P2 P1, npost-#}"
    by blast
qed


(*
lemma HTS_imp_HT'' :
  assumes H: "f % {{P1}} c {{P2}}"
  assumes Valid : "lifting_valid l S"
  assumes Hf' : "f' = no_control_l l f"
  assumes H0 : "gs = pcomps fs"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hseq : "seq_sem_l_gen lfts \<in> set fs"
  assumes Skip : "lfts c = Sskip"
  assumes Hnemp : "g \<in> (set fs - {seq_sem_l_gen lfts})"
  assumes Hdom : "(f' \<downharpoonleft> (set fs - {seq_sem_l_gen lfts}) c)"
  shows "|gs| {~ (lift_pred_s id l c P1) ~} [G c z] {~ (lift_pred_s id l c P2) ~}"
proof(rule HT'I)
  fix npost

  have "|#gs#| {#-lift_pred_s id l c
                     P1, (0 +
                          npost)-#} [G c z] {#-lift_pred_s id l c
       P2, npost-#}"
    unfolding add_0
  proof
    fix c'

    assume Guard : "|#gs#| {#lift_pred_s id l c P2, npost#} c'"
    show "|#gs#| {#lift_pred_s id l c P1, npost#} ([G c z] @ c')"
    proof
      fix m :: "('a, 'c) control"
      assume Hpay : "lift_pred_s id l c P1 (payload m)"
      assume Hcont : "cont m = Inl ([G c z] @ c') "

      have Hpay1 : "P1 (LOut l c (payload m))" 
        using Hpay
        unfolding lift_pred_valid_s_def lift_pred_s_def
        by auto
(*
      have Hpay' : "(P2 (f c (payload m)))"
        using HTSE[OF H Hpay] by auto
*)
      have Hpay' : "P2 (f c (LOut l c (payload m)))"
        using HTSE[OF H Hpay1]
        by simp

      show "safe_for gs m npost"
      proof(cases "(sem_step gs m)")
        case (Inr bad)
  
        then have False using Hcont H0
          by(auto simp add: sem_step_def)
  
        then show ?thesis by auto
      next
        case (Inl m')

        have Pres' : "sups_pres (set fs - {seq_sem_l_gen lfts})"
          using sups_pres_subset[OF Hpres, of "set fs - {seq_sem_l_gen lfts}"] by auto

        obtain fs_sub where Fs_sub : "set fs_sub = set fs - {seq_sem_l_gen lfts}"
          using finite_list[of "set fs - {seq_sem_l_gen lfts}"]
          by auto

(* ok, so the idea now is:
- we know full step (op + control flow) leads to m'
- dominance over everything but the seq means we can treat it as
  "op (dominant thing) then seq"
- we can then unfold these things in order and everything should be ok.
*)

        have Assoc : 
             "pcomps (fs_sub @ [seq_sem_l_gen lfts]) =
              pcomps [pcomps fs_sub, pcomps [seq_sem_l_gen lfts]]"
        proof(rule pcomps_assoc)

          have "set fs - {seq_sem_l_gen lfts} \<union> set [seq_sem_l_gen lfts] = set fs"
            using Hseq 
            by(simp; blast)

          then show "sups_pres (set fs_sub \<union> set [seq_sem_l_gen lfts])"
            unfolding Fs_sub
            using Hpres
            by auto
        next

          have "set fs_sub \<noteq> {}" using Hnemp unfolding Fs_sub by auto

          then show "fs_sub \<noteq> []" by auto
        next

          show "[seq_sem_l_gen lfts] \<noteq> []" by simp
        qed

        have Set_alt : "set (fs_sub @ [seq_sem_l_gen lfts]) = set fs"
          unfolding set_append Fs_sub
          using Un_Diff_cancel2 Hseq
          by auto

        have Gs_alt : "gs = pcomps (fs_sub @ [seq_sem_l_gen lfts])"
          using pcomps_set_eq[OF Hpres Hseq _ Set_alt, of fs] H0
          by auto
          
(* TODO: find a better solution than this awful type annotation hack *)
        have Seq_pres : 
          "sups_pres {(seq_sem_l_gen lfts  :: ('a \<Rightarrow> 'a gensyn list md_triv option md_prio \<times>
            String.literal md_triv option md_prio \<times> 'c
            \<Rightarrow> 'a gensyn list md_triv option md_prio \<times>
               String.literal md_triv option md_prio \<times>
               'c))}"
          using sups_pres_subset[OF Hpres, of "{seq_sem_l_gen lfts}"] Hseq
          by(auto)


        have Gs_alt' : "gs = pcomps [pcomps fs_sub, seq_sem_l_gen lfts]"
          using Gs_alt pcomps_singleton[OF Seq_pres, of "[seq_sem_l_gen lfts]"]
          unfolding Assoc
          unfolding append.simps H0
          by auto

        have Hdom' :  "f' \<downharpoonleft> (set fs_sub) c"
          using Fs_sub Hdom by auto
        have Dominate1 : "pcomps fs_sub c m = f' c m" using dominant_pcomps[OF _ _ Hdom', of g m] Pres' Hnemp Fs_sub
          by auto

(* almost have this. the missing ingredient is using the fact that
 * information content will increase (for a strong-valid lifting) *)

(* TODO: declare a lemmas with all the definitions of liftings... *)
        obtain pri1 pri2 rest where Msplit :
          "m = (mdp pri1 (Some (mdt (G c z # c'))), mdp pri2 None, rest)"
          and Rest : "rest \<in> S c"
          using Gs_alt' Dominate1 Skip Hpay Hcont Hf'
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def 
            lift_pred_valid_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)

        have LUpd_rest1 :
          "rest <[ LUpd l c (f c (LOut l c rest)) rest"
          using lifting_validDI[OF Valid Rest]
          by auto
(* TODO: I think the problem here is that we actually need to use the fact that we want a more
restricted set than just what we are valid on... *)
        have LUpd_rest2 : "[^ LUpd l c (f c (LOut l c rest)) rest, rest ^] = LUpd l c (f c (LOut l c rest)) rest"
          using bsup_base_leq2[OF LUpd_rest1]
          by simp

        then have LOut_m : "LOut (no_control_lifting l) c (gs c m) = LOut (no_control_lifting l) c (f' c m)"
          using Gs_alt' Dominate1 Skip Hpay Hcont Hf' Msplit
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def 
            lift_pred_valid_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)


(* key sub-result. *)
        have Pay_final : "payload m' = LUpd l c (f c (LOut l c (payload m))) (payload m)"
          using Gs_alt' Dominate1 Skip Hpay Hcont Hf' Msplit Inl LUpd_rest2
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            lift_pred_valid_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)

(* key sub-result. idea here is that no_control_l means we won't overwrite. *)
        have Cont_final : "cont m' = cont (seq_sem_l_gen lfts c m)"
          using Hcont Msplit Skip Inl Gs_alt' Dominate1 Hf'
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            lift_pred_valid_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def prio_bsup option_bsup leq_refl
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)         

        hence Cont_final' : "cont m' = Inl c'"
          using Hcont Msplit Skip
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            lift_pred_valid_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)

        have Conc' : "safe_for gs m' npost"
          using guardediD[OF Guard, of "m'"] Hpay' Cont_final'
          unfolding Pay_final Cont_final' lift_pred_valid_s_def lift_pred_s_def
          using lifting_validDO[OF Valid] lifting_validDP[OF Valid]
          by(cases m; auto)

        have Inl_alt : "sem_step_p gs m m'"
          using Inl unfolding sem_step_p_eq by simp

        show  "safe_for gs m npost"
          using safe_for_weaken[OF safe_for_extend[OF Conc' Excp_1[OF Inl_alt]], of npost]
          by simp
      qed
    qed
  qed

  thus "\<exists>npre.
          |#gs#| {#-lift_pred_valid_s id l S c
                     P1, (npre + npost)-#} [G c z] {#-lift_pred_valid_s id l S c P2, npost-#}"
    by blast
qed
*)

end