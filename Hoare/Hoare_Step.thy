theory Hoare_Step imports Hoare Hoare_Indexed Hoare_Direct
 "../Lifter/Auto_Lifter_Proofs"
 "../Mergeable/Mergeable_Instances"
 "../Composition/Composition" "../Composition/Dominant"
 "../Language_Components/Seq/Seq_Hoare"
 "Hoare_Lift" "Hoare_Lift_Transform" "../Lifter/Toggle"
begin

(* 
 * When dealing with single-step languages, we have an important special case - that is,
 * the case where the single-step language is _dominant_ (see Composition/Dominant.thy)
 * for one or more pieces of syntax. In such cases we can show that the
 * lifted version of the rule holds without side conditions.
 *)

(* TODO - decouple this from seq *)

(* However, we might be able to avoid reasoning about liftings at all in such cases (?)
 * by playing the same parametricity trick as with the control languages?
 *)

definition no_control_lifting :: "('a, 'b1, 'b2 :: {Bogus, Pord}) lifting \<Rightarrow>
  ('a, 'b1, ('x, 'b2) control) lifting" where
"no_control_lifting l =
  schem_lift NC (SP NX (SP NX (SINJ l NC)))"


definition no_control_lifting_S ::"
('a, 'b1, 'b2 :: {Bogus, Pord}) lifting \<Rightarrow>
  ('a \<Rightarrow> 'b2 set) \<Rightarrow>
  ('a \<Rightarrow> ('x, 'b2) control set)" where
"no_control_lifting_S l S =
  schem_lift_S NC (SP NX (SP NX (SINJS l S NC)))"

(* something is weird with the pord constraint here. *)
definition no_control_l :: "
('a, 'b1, 'b2 :: {Bogus, Pord, Okay}) lifting \<Rightarrow>
('a \<Rightarrow> 'b1 \<Rightarrow> 'b1 :: {Bogus, Pord, Okay}) \<Rightarrow>
('a \<Rightarrow> ('x, 'b2 :: {Bogus, Pord, Okay}) control \<Rightarrow> ('x, 'b2 ) control)" where
"no_control_l l f =
  lift_map_s id (no_control_lifting l) f"

lemma no_control_l_valid :
  assumes H : "lifting_valid_ok l S"
  shows "lifting_valid_ok (no_control_lifting l) (no_control_lifting_S l S)"
  using H
  unfolding no_control_lifting_def no_control_lifting_S_def schem_lift_defs schem_lift_S_defs
  by(fastforce intro: lifting_valid_fast lifting_ortho_fast
  dest: lifting_valid_locale_axioms
)
  (*
lemma HTS_imp_HT' :
  fixes fs :: "('b \<Rightarrow> ('b, 'c) control \<Rightarrow> ('b, 'c :: {Bogus, Mergeableb, Okay}) control) list"
  assumes H: "f % {{P1}} c {{P2}}"
  assumes Valid : "lifting_valid_ok l S"
  assumes Hf' : "f' = no_control_l l f"
  assumes H0 : "gs = pcomps fs"
  (* was payload ` ok_S *)
(*
  assumes Hpres : "sups_pres (set fs) (\<lambda> _ . (ok_S :: ('b, 'c) control set))"

*)
  assumes Hpres : "sups_pres (set fs) (\<lambda> _ . (ok_S :: ('b, 'c) control set))"
  assumes Hseq : "seq_sem_l_gen lfts \<in> set fs"
  assumes Skip : "lfts c = Sskip"
  assumes Cin : "c \<in> X"
  assumes Hnemp : "g \<in> (set fs - {seq_sem_l_gen lfts})"
  assumes Hdom : "(f' \<down> (set fs - {seq_sem_l_gen lfts}) X)"
  shows "|gs| {~ (lift_pred_valid_ok_s id l c P1) ~} [G c z] {~ (lift_pred_valid_ok_s id l c P2) ~}"
proof(rule HT'I)
  fix npost

  interpret V: lifting_valid_ok l S
    using Valid .

  have "|#gs#| {#-lift_pred_valid_ok_s id l c
                     P1, (0 +
                          npost)-#} [G c z] {#-lift_pred_valid_ok_s id l c
       P2, npost-#}"
    unfolding add_0
  proof
    fix c'

    assume Guard : "|#gs#| {#lift_pred_valid_ok_s id l c P2, npost#} c'"
    show "|#gs#| {#lift_pred_valid_ok_s id l c P1, npost#} ([G c z] @ c')"
    proof
      fix m :: "('b, 'c) control"
      assume Ok : "m \<in> ok_S"
      assume Hpay : "lift_pred_valid_ok_s id l c P1 (payload m)"
      assume Hcont : "cont m = Inl ([G c z] @ c') "

      have Hpay1 : "P1 (LOut l c (payload m))" and Hpay2 : "payload m \<in> S c" and Hpay3 : "payload m \<in> ok_S"
        using Hpay 
        using V.ok_S_valid
        unfolding lift_pred_valid_ok_s_def 
        unfolding lift_pred_noS_s_def lift_pred_s_def
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

        have Huh : "set fs - {seq_sem_l_gen lfts} \<subseteq> set fs" "finite (set fs)"
          by auto
        have Pres' : "sups_pres (set fs - {seq_sem_l_gen lfts}) (\<lambda> _ . ok_S)"
          (*using sups_pres_subset[OF Hpres, of "set fs - {seq_sem_l_gen lfts}"] Hnemp by auto*)
          using sups_pres_subset[OF Hpres Huh(2) Huh(1) Hnemp]
          by(auto)
          

        obtain fs_sub where Fs_sub : "set fs_sub = set fs - {seq_sem_l_gen lfts}"
          using finite_list[of "set fs - {seq_sem_l_gen lfts}"]
          by auto

(* ok, so the idea now is:
- we know full step (op + control flow) leads to m'
- dominance over everything but the seq means we can treat it as
  "op (dominant thing) then seq"
- we can then unfold these things in order and everything should be ok.
*)

(* this does not hold in general now - need to use some information about the input. *)
(* gs c m specifically is all we need *)

        have Assoc : 
             "pcomps (fs_sub @ [seq_sem_l_gen lfts]) c m =
              pcomps [pcomps fs_sub, pcomps [seq_sem_l_gen lfts]] c m"
        proof(rule pcomps_assoc[where S = "\<lambda> _ . ok_S"])

          have "set fs - {seq_sem_l_gen lfts} \<union> set [seq_sem_l_gen lfts] = set fs"
            using Hseq 
            by(simp; blast)

          then show "\<And> s x . sups_pres (set fs_sub \<union> set [seq_sem_l_gen lfts]) (\<lambda> _ . ok_S)"
            unfolding Fs_sub
            using Hpres
            by auto
        next

          have "set fs_sub \<noteq> {}" using Hnemp unfolding Fs_sub by auto

          then show "fs_sub \<noteq> []" by auto
        next

          show "[seq_sem_l_gen lfts] \<noteq> []" by simp
        next
          show "m \<in> ok_S"
            using Ok .
        qed

        have Set_alt : "set (fs_sub @ [seq_sem_l_gen lfts]) = set fs"
          unfolding set_append Fs_sub
          using Un_Diff_cancel2 Hseq
          by auto

        have Gs_alt : "gs c m = pcomps (fs_sub @ [seq_sem_l_gen lfts]) c m"
          using pcomps_set_eq[OF Hpres Hseq _ Set_alt Ok, of fs] H0
          by auto
          
(* TODO: find a better solution than this awful type annotation hack *)
        have Seq_pres : 
          "sups_pres {(seq_sem_l_gen lfts  :: ('b \<Rightarrow> 'b gensyn list md_triv option md_prio \<times>
            String.literal md_triv option md_prio \<times> 'c
            \<Rightarrow> 'b gensyn list md_triv option md_prio \<times>
               String.literal md_triv option md_prio \<times>
               'c))} (\<lambda> _ . ok_S)"
          using sups_pres_subset[OF Hpres, of "{seq_sem_l_gen lfts}"] Hseq
          by(auto)

        have Gs_alt' : "gs c m = pcomps [pcomps fs_sub, seq_sem_l_gen lfts] c m"
          using Gs_alt pcomps_singleton[OF Seq_pres _ Ok, of "[seq_sem_l_gen lfts]"]
          unfolding Assoc
          unfolding append.simps H0
          by auto

        have Hdom' :  "f' \<down> (set fs_sub) X"
          using Fs_sub Hdom by auto

        have Dominate1 : "pcomps fs_sub c m = f' c m" 
          using dominant_pcomps[OF Pres'[folded Fs_sub] _ Hdom' Cin Ok] Pres' Hnemp Fs_sub
          by auto

(* almost have this. the missing ingredient is using the fact that
 * information content will increase (for a strong-valid lifting) *)

(* TODO: declare a lemmas with all the definitions of liftings... *)
        obtain pri1 pri2 rest where Msplit :
          "m = (mdp pri1 (Some (mdt (G c z # c'))), mdp pri2 (Some (mdt (STR ''''))), rest)"
          and Rest : "rest \<in> ok_S"
          using (*Gs_alt'*) Dominate1 Skip Hpay Hcont Hf'
          unfolding lift_pred_valid_ok_s_def lift_pred_noS_s_def

          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def 
            lift_pred_s_def lift_pred_valid_ok_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm if_splits)

(* need m' \<in> ok_S *)
        have Rest' : "rest \<in> ok_S"
          using Rest by auto

        hence Rest'' : "rest \<in> S c"
          using V.ok_S_valid
          by auto

        have LUpd_rest1 :
          "rest <[ LUpd l c (f c (LOut l c rest)) rest"
          using V.get_put
          by auto

        have LUpd_rest2 : "[^ LUpd l c (f c (LOut l c rest)) rest, rest ^] = LUpd l c (f c (LOut l c rest)) rest"
          using bsup_base_leq2[OF LUpd_rest1]
          by simp

        then have LOut_m : "LOut (no_control_lifting l) c (gs c m) = LOut (no_control_lifting l) c (f' c m)"
          using Gs_alt' Dominate1 Skip Hpay Hcont Hf' Msplit
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def  lift_map_s_def
            lift_pred_valid_ok_s_def lift_pred_s_def lift_pred_noS_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm if_splits)


(* key sub-result. *)
        have Pay_final : "payload m' = LUpd l c (f c (LOut l c (payload m))) (payload m)"
          using Gs_alt' Dominate1 Skip Hpay Hcont Hf' Msplit Inl LUpd_rest2
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            seq_sem_lifting_gen_def  lift_map_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)

(* key sub-result. idea here is that no_control_l means we won't overwrite. *)
        have Cont_final : "cont m' = cont (seq_sem_l_gen lfts c m)"
          using Hcont Msplit Skip Inl Gs_alt' Dominate1 Hf'
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            seq_sem_lifting_gen_def  lift_map_s_def lift_pred_s_def lift_pred_noS_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup triv_bsup no_control_l_def prio_bsup option_bsup leq_refl
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm if_splits)         

        hence Cont_final' : "cont m' = Inl c'"
          using Hcont Msplit Skip
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            seq_sem_lifting_gen_def  lift_map_s_def lift_pred_s_def lift_pred_noS_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup triv_bsup no_control_l_def prio_bsup option_bsup leq_refl
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm if_splits)         

        have Rest'_ok : "LUpd l c (f c (LOut l c rest)) rest \<in> ok_S"
          using V.ok_S_put[OF Rest']
          by auto

(* the priority being unchanged when updating the control data seems off. *)
        then have Ok' : "m' \<in> ok_S"
          using Gs_alt' Dominate1 Skip Hpay Hcont Hf' Msplit Inl LUpd_rest2 Rest' Ok
          apply(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            seq_sem_lifting_gen_def  lift_map_s_def lift_pred_s_def lift_pred_noS_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup triv_bsup no_control_l_def prio_bsup option_bsup leq_refl
            prod_ok_S option_ok_S triv_ok_S prio_ok_S
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm if_splits)  
(* this sucks. *)
          apply(rule_tac x =  "mdp (Suc pri1) (Some (mdt c'))" in exI)
          apply(rule_tac x = "mdp pri2 (Some (mdt (STR '''')))" in exI)
          apply(rule_tac x = "LUpd l c (f c (LOut l c rest)) rest" in exI)
          by(auto)

        have Conc' : "safe_for gs m' npost"
          using guardediD[OF Guard Ok'] Hpay' Cont_final' Rest'_ok Ok' Hpay3
          unfolding Pay_final Cont_final' lift_pred_s_def lift_pred_noS_s_def lift_pred_valid_ok_s_def lift_pred_s_def
          using V.put_get[ of c "f c (LOut l c (payload m))" "payload m"] V.ok_S_put
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
          |#gs#| {#-lift_pred_valid_ok_s id l c
                     P1, (npre + npost)-#} [G c z] {#-lift_pred_valid_ok_s id l c P2, npost-#}"
    by blast
qed
*)

lemma HTS_imp_HT'' :
  fixes fs :: "('b \<Rightarrow> ('b, 'c) control \<Rightarrow> ('b, 'c :: {Bogus, Mergeableb, Okay}) control) list"
(*
  fixes f :: "'syn0 \<Rightarrow> 'st0 \<Rightarrow> 'st0"
  fixes x :: "'syn1"
  fixes l' :: "('syn1 \<Rightarrow> 'syn0)"
*)
  assumes H: "f % {{P'}} (l' x) {{Q'}}"
  (* TODO: can we weaken this to lifting_valid_weak_ok *)
  assumes Valid : "lifting_valid_ok l S"
  assumes Hf' : "f' = lift_map_t_s l' (no_control_lifting  l) tg f"
  assumes H0 : "gs = pcomps fs"
  assumes Hpres : "sups_pres (set fs) (\<lambda> _ . ok_S)"
  assumes Hseq : "seq_sem_l_gen lfts \<in> set fs"
  assumes Skip : "lfts x = Sskip"
  assumes Active : "tg x = True"
  assumes Xin : "x \<in> X"
  assumes Hnemp : "g \<in> (set fs - {seq_sem_l_gen lfts})"
  assumes Hdom : "(f' \<down> (set fs - {seq_sem_l_gen lfts}) X)"
  assumes HP : "\<And> st . P st \<Longrightarrow> P' (LOut l (l' x) st)"

  shows "|gs| {~ (\<lambda> st . P st) ~} [G x z] 
    {~ (\<lambda> st . \<exists> old_big small_new . P old_big \<and> Q' small_new \<and> st = LUpd l (l' x) small_new old_big) ~}"
  (*shows "\<And> P1 . |gs| {~ P1 ~} [G c z] {~ (liftt_conc id l c P2 P1) ~}"*)
proof(rule HT'I)
  fix npost

  interpret V : lifting_valid_ok l S
    using Valid .

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
      fix m :: "('b, 'c) control"
      assume Ok : "m \<in> ok_S"
      assume Hpay0 : "P (payload m)" and Hcont : "cont m = Inl ([G x z] @ c') "

      show "safe_for gs m npost"
      proof(cases "(sem_step gs m)")
        case (Inr bad)
  
        then have False using Hcont H0
          by(auto simp add: sem_step_def)
  
        then show ?thesis by auto
      next
        case (Inl m')

        have Pres' : "sups_pres (set fs - {seq_sem_l_gen lfts}) (\<lambda> _ . ok_S)"
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
             "pcomps (fs_sub @ [seq_sem_l_gen lfts]) x m =
              pcomps [pcomps fs_sub, pcomps [seq_sem_l_gen lfts]] x m"
        proof(rule pcomps_assoc)

          have "set fs - {seq_sem_l_gen lfts} \<union> set [seq_sem_l_gen lfts] = set fs"
            using Hseq 
            by(simp; blast)

          then show "sups_pres (set fs_sub \<union> set [seq_sem_l_gen lfts]) (\<lambda> _ . ok_S)"
            unfolding Fs_sub
            using Hpres
            by auto
        next

          have "set fs_sub \<noteq> {}" using Hnemp unfolding Fs_sub by auto

          then show "fs_sub \<noteq> []" by auto
        next

          show "[seq_sem_l_gen lfts] \<noteq> []" by simp
        next
          show "m \<in> ok_S"
            using Ok .
        qed

        have Set_alt : "set (fs_sub @ [seq_sem_l_gen lfts]) = set fs"
          unfolding set_append Fs_sub
          using Un_Diff_cancel2 Hseq
          by auto

        have Gs_alt : "gs x m = pcomps (fs_sub @ [seq_sem_l_gen lfts]) x m"
          using pcomps_set_eq[OF Hpres Hseq _ Set_alt Ok, of fs] H0
          by auto

        have Hpay : "P (payload m)"
          using Hpay0
          by auto

        then have Hpay_S : "payload m \<in> ok_S"
          using Ok by(cases m; auto simp add: prod_ok_S)

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
          "sups_pres {(seq_sem_l_gen lfts  ::('b \<Rightarrow> 'b gensyn list md_triv option md_prio \<times>
            String.literal option md_triv option md_prio \<times> 'c
            \<Rightarrow> 'b gensyn list md_triv option md_prio \<times>
               String.literal option md_triv option md_prio \<times>
               'c))} (\<lambda> _ . ok_S)"
          using sups_pres_subset[OF Hpres, of "{(seq_sem_l_gen lfts )}"] Hseq
          by(auto)

        have Gs_alt' : "gs x m = pcomps [pcomps fs_sub, seq_sem_l_gen lfts] x m"
          using Gs_alt pcomps_singleton[OF Seq_pres _ Ok, of "[seq_sem_l_gen lfts]"]
          unfolding Assoc
          unfolding append.simps H0
          by auto

        have Hdom' :  "f' \<down> (set fs_sub) X"
          using Fs_sub Hdom by auto

        have Dominate1 : "pcomps fs_sub x m = f' x m"
          using dominant_pcomps[OF Pres'[unfolded sym[OF Fs_sub]] Hnemp[unfolded sym[OF Fs_sub]] Hdom' Xin Ok]
          by auto
        obtain pri1 pri2 rest where Msplit :
          "m = (mdp pri1 (Some (mdt (G x z # c'))), mdp pri2 (Some (mdt None)), rest)" and Rest : "rest \<in> ok_S"
          using Gs_alt' Dominate1 (*Dominate1_weak*) Skip Hpay Hcont Hf' Hpay_S
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def 
            lift_pred_valid_ok_s_def lift_pred_noS_s_def lift_pred_s_def lift_map_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm if_splits)

        have Rest' : "rest \<in> S (l' x)"
          using V.ok_S_valid Rest by auto

        have LUpd_rest1 :
          "rest <[ LUpd l (l' x) (f (l' x) (LOut l (l' x) rest)) rest"
          using 
            V.get_put
          by auto

        have LUpd_rest2 : "[^ LUpd l (l' x) (f (l' x) (LOut l (l' x) rest)) rest, rest ^] = LUpd l (l' x) (f (l' x) (LOut l (l' x) rest)) rest"
          using bsup_base_leq2[OF LUpd_rest1]
          by simp

(*
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
*)

(* key sub-result. *)

(* key sub-result. idea here is that no_control_l means we won't overwrite. *)
        have Cont_final : "cont m' = cont (seq_sem_l_gen lfts x m)"
          using Hcont Msplit Skip Inl Gs_alt' Dominate1 Hf' Msplit
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            lift_pred_s_def lift_map_s_def lift_map_t_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def prio_bsup option_bsup leq_refl triv_bsup split: md_prio.splits if_splits md_triv.splits option.splits)
(*
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)         
*)
        hence Cont_final' : "cont m' = Inl c'"
          using Hcont Msplit Skip
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            lift_map_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)

        have Pay_final : "payload m' = LUpd l (l' x) (f (l' x) (LOut l (l' x) (payload m))) (payload m)"
          using Gs_alt' Dominate1 Skip Hpay Hcont Hf' Msplit Inl LUpd_rest2 Active
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            lift_map_s_def lift_map_t_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)


        have "(P (payload m)) \<and> Q' ((f (l' x) (LOut l (l' x) (payload m)))) \<and>
              payload m' = LUpd l (l' x) (f (l' x) (LOut l (l' x) (payload m)))(payload m)"
          using Hpay' Pay_final Hpay_S Hpay
          by(auto)

        then have Guard_Hyp : "\<exists>old_big small_new.
             P old_big \<and>
             Q' small_new \<and>
             payload m' = LUpd l (l' x) small_new old_big"
          by auto

        have M'_ok : "m' \<in> ok_S"
          using Hcont Msplit Skip Inl Gs_alt' Dominate1 Hf' Msplit Cont_final' Pay_final
            V.ok_S_put[OF Rest]
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            lift_pred_s_def lift_map_s_def lift_map_t_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def prio_bsup option_bsup leq_refl triv_bsup
            prod_ok_S triv_ok_S prio_ok_S option_ok_S
            split: md_prio.splits if_splits md_triv.splits option.splits)

        have Conc' : "safe_for gs m' npost"
          using guardediD[OF Guard, of "m'"]  Cont_final' Guard_Hyp
          using M'_ok
          unfolding Pay_final Cont_final' lift_pred_s_def lift_pred_s_def lift_pred_valid_ok_s_def
            liftt_conc_def
          
          (*using lifting_validDO[OF Valid'] lifting_validDP[OF Valid'] lifting_validxDP'[OF Valid ]*)
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


lemma HTS_imp_HT''' :
  fixes fs :: "('b \<Rightarrow> ('b, 'c) control \<Rightarrow> ('b, 'c :: {Bogus, Mergeableb, Okay}) control) list"
  assumes H: "f % {{P'}} (l' x) {{Q'}}"
  (* TODO: can we weaken this to lifting_valid_weak_ok *)
  assumes Valid : "lifting_valid_ok l S"
  assumes Hf' : "f' = lift_map_t_s l' (no_control_lifting  l) tg f"
  assumes H0 : "gs = pcomps fs"
  assumes Hpres : "sups_pres (set fs) (\<lambda> _ . ok_S)"
  assumes Hseq : "seq_sem_l_gen lfts \<in> set fs"
  assumes Skip : "lfts x = Sskip"
  assumes Active : "tg x = True"
  assumes Xin : "x \<in> X"
  assumes Hnemp : "g \<in> (set fs - {seq_sem_l_gen lfts})"
  assumes Hdom : "(f' \<down> (set fs - {seq_sem_l_gen lfts}) X)"
  assumes HP : "\<And> st . P st \<Longrightarrow> P' (LOut l (l' x) st)"

  shows "|gs| {~ (\<lambda> st . P st) ~} [G x z] 
    {~ (\<lambda> st . \<exists> old_big . P old_big \<and> 
        P' (LOut l (l' x) old_big) \<and>
        Q' (LOut l (l' x) st) \<and> 
        st = LUpd l (l' x) (f (l' x) (LOut l (l' x) old_big)) old_big)
         ~}"
(*
{~ (\<lambda> st . \<exists> old_big small_new . P old_big \<and> (case small_new of
                                  (c1, c2, x) \<Rightarrow> x = c1 + c2 \<and> 
(\<exists>old. P' (c1, c2, old) \<and> LOut calc_lift' Cadd old_big = (c1, c2, old))) \<and>
                                 st = LUpd calc_lift' Cadd small_new old_big) ~}
*)
  (*shows "\<And> P1 . |gs| {~ P1 ~} [G c z] {~ (liftt_conc id l c P2 P1) ~}"*)
proof(rule HT'I)
  fix npost

  interpret V : lifting_valid_ok l S
    using Valid .

  have "|#gs#| {#-(\<lambda>st. P st), (0 + npost)-#} [G x z] {#-(\<lambda>st. \<exists>old_big.
                 P old_big \<and>
                 P' (LOut l (l' x) old_big) \<and>
                 Q' ((LOut l (l' x) st)) \<and>
                 st = LUpd l (l' x) (f (l' x) (LOut l (l' x) old_big)) old_big), npost-#}"
    unfolding add_0
  proof
    fix c'

    assume Guard : " |#gs#| {#(\<lambda>st. \<exists>old_big.
                 P old_big \<and>
                 P' (LOut l (l' x) old_big) \<and>
                 Q' ((LOut l (l' x) st)) \<and>
                 st = LUpd l (l' x) (f (l' x) (LOut l (l' x) old_big)) old_big), npost#} c'"
    show "|#gs#| {#P, npost#} ([G x z] @ c')"
    proof
      fix m :: "('b, 'c) control"
      assume Ok : "m \<in> ok_S"
      assume Hpay0 : "P (payload m)" and Hcont : "cont m = Inl ([G x z] @ c') "

      show "safe_for gs m npost"
      proof(cases "(sem_step gs m)")
        case (Inr bad)
  
        then have False using Hcont H0
          by(auto simp add: sem_step_def)
  
        then show ?thesis by auto
      next
        case (Inl m')

        have Pres' : "sups_pres (set fs - {seq_sem_l_gen lfts}) (\<lambda> _ . ok_S)"
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
             "pcomps (fs_sub @ [seq_sem_l_gen lfts]) x m =
              pcomps [pcomps fs_sub, pcomps [seq_sem_l_gen lfts]] x m"
        proof(rule pcomps_assoc)

          have "set fs - {seq_sem_l_gen lfts} \<union> set [seq_sem_l_gen lfts] = set fs"
            using Hseq 
            by(simp; blast)

          then show "sups_pres (set fs_sub \<union> set [seq_sem_l_gen lfts]) (\<lambda> _ . ok_S)"
            unfolding Fs_sub
            using Hpres
            by auto
        next

          have "set fs_sub \<noteq> {}" using Hnemp unfolding Fs_sub by auto

          then show "fs_sub \<noteq> []" by auto
        next

          show "[seq_sem_l_gen lfts] \<noteq> []" by simp
        next
          show "m \<in> ok_S"
            using Ok .
        qed

        have Set_alt : "set (fs_sub @ [seq_sem_l_gen lfts]) = set fs"
          unfolding set_append Fs_sub
          using Un_Diff_cancel2 Hseq
          by auto

        have Gs_alt : "gs x m = pcomps (fs_sub @ [seq_sem_l_gen lfts]) x m"
          using pcomps_set_eq[OF Hpres Hseq _ Set_alt Ok, of fs] H0
          by auto

        have Hpay : "P (payload m)"
          using Hpay0
          by auto

        then have Hpay_S : "payload m \<in> ok_S"
          using Ok by(cases m; auto simp add: prod_ok_S)

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
          "sups_pres {(seq_sem_l_gen lfts  ::('b \<Rightarrow> 'b gensyn list md_triv option md_prio \<times>
            String.literal option md_triv option md_prio \<times> 'c
            \<Rightarrow> 'b gensyn list md_triv option md_prio \<times>
               String.literal option md_triv option md_prio \<times>
               'c))} (\<lambda> _ . ok_S)"
          using sups_pres_subset[OF Hpres, of "{(seq_sem_l_gen lfts )}"] Hseq
          by(auto)

        have Gs_alt' : "gs x m = pcomps [pcomps fs_sub, seq_sem_l_gen lfts] x m"
          using Gs_alt pcomps_singleton[OF Seq_pres _ Ok, of "[seq_sem_l_gen lfts]"]
          unfolding Assoc
          unfolding append.simps H0
          by auto

        have Hdom' :  "f' \<down> (set fs_sub) X"
          using Fs_sub Hdom by auto

        have Dominate1 : "pcomps fs_sub x m = f' x m"
          using dominant_pcomps[OF Pres'[unfolded sym[OF Fs_sub]] Hnemp[unfolded sym[OF Fs_sub]] Hdom' Xin Ok]
          by auto
        obtain pri1 pri2 rest where Msplit :
          "m = (mdp pri1 (Some (mdt (G x z # c'))), mdp pri2 (Some (mdt None)), rest)" and Rest : "rest \<in> ok_S"
          using Gs_alt' Dominate1 (*Dominate1_weak*) Skip Hpay Hcont Hf' Hpay_S
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def 
            lift_pred_valid_ok_s_def lift_pred_noS_s_def lift_pred_s_def lift_map_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm if_splits)

        have Rest' : "rest \<in> S (l' x)"
          using V.ok_S_valid Rest by auto

        have LUpd_rest1 :
          "rest <[ LUpd l (l' x) (f (l' x) (LOut l (l' x) rest)) rest"
          using 
            V.get_put
          by auto

        have LUpd_rest2 : "[^ LUpd l (l' x) (f (l' x) (LOut l (l' x) rest)) rest, rest ^] = LUpd l (l' x) (f (l' x) (LOut l (l' x) rest)) rest"
          using bsup_base_leq2[OF LUpd_rest1]
          by simp

(*
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
*)

(* key sub-result. *)

(* key sub-result. idea here is that no_control_l means we won't overwrite. *)
        have Cont_final : "cont m' = cont (seq_sem_l_gen lfts x m)"
          using Hcont Msplit Skip Inl Gs_alt' Dominate1 Hf' Msplit
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            lift_pred_s_def lift_map_s_def lift_map_t_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def prio_bsup option_bsup leq_refl triv_bsup split: md_prio.splits if_splits md_triv.splits option.splits)
(*
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)         
*)
        hence Cont_final' : "cont m' = Inl c'"
          using Hcont Msplit Skip
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            lift_map_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)

        have Pay_final : "payload m' = LUpd l (l' x) (f (l' x) (LOut l (l' x) (payload m))) (payload m)"
          using Gs_alt' Dominate1 Skip Hpay Hcont Hf' Msplit Inl LUpd_rest2 Active
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            lift_map_s_def lift_map_t_s_def lift_pred_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def
            split: md_prio.splits prod.splits md_triv.splits option.splits list.split_asm)


        have "(P (payload m)) \<and> Q' ((f (l' x) (LOut l (l' x) (payload m)))) \<and>
              payload m' = LUpd l (l' x) (f (l' x) (LOut l (l' x) (payload m)))(payload m)"
          using Hpay' Pay_final Hpay_S Hpay
          by(auto)

        then have Guard_Hyp : "\<exists>old_big.
           P old_big \<and>
           P' (LOut l (l' x) old_big) \<and>
           Q' (LOut l (l' x) (payload m')) \<and>
           payload m' = LUpd l (l' x) (f (l' x) (LOut l (l' x) old_big)) old_big"
          apply(rule_tac x = "(payload m)" in exI)
          by(cases m; cases m'; auto simp add: V.put_get HP)
          

        have M'_ok : "m' \<in> ok_S"
          using Hcont Msplit Skip Inl Gs_alt' Dominate1 Hf' Msplit Cont_final' Pay_final
            V.ok_S_put[OF Rest]
          by(auto simp add: seq_sem_l_gen_def seq_sem_lifting_gen_def sem_step_def
            lift_pred_s_def lift_map_s_def lift_map_t_s_def
            no_control_lifting_def cont_def
            schem_lift_defs fst_l_def snd_l_def prio_l_def triv_l_def option_l_def seq_sem_def
            prod_bsup no_control_l_def prio_bsup option_bsup leq_refl triv_bsup
            prod_ok_S triv_ok_S prio_ok_S option_ok_S
            split: md_prio.splits if_splits md_triv.splits option.splits)

        have Conc' : "safe_for gs m' npost"
          using guardediD[OF Guard, of "m'"]  Cont_final' Guard_Hyp
          using M'_ok
          unfolding Pay_final Cont_final' lift_pred_s_def lift_pred_s_def lift_pred_valid_ok_s_def
            liftt_conc_def
          
          (*using lifting_validDO[OF Valid'] lifting_validDP[OF Valid'] lifting_validxDP'[OF Valid ]*)
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
                        npost)-#} [G x z] {#-(\<lambda>st.
            \<exists>old_big.
               P old_big \<and>
               P' (LOut l (l' x) old_big) \<and>
               Q' (LOut l (l' x) st) \<and>
               st =
               LUpd l (l' x) (f (l' x) (LOut l (l' x) old_big))
                old_big), npost-#}"
    by blast
qed


end