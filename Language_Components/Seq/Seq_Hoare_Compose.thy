theory Seq_Hoare_Compose
  imports Seq_Hoare "../../Hoare/Hoare_Direct" "../../Lifter/Auto_Lifter_Proofs" "../../Hoare/Hoare_Lift"
begin

(*
 * Without some notion of control, we can't have CPS-style Hoare rules for 
 * our single-step semantics.
 * 
 * Idea: let's use INJ here instead.
 *)

definition no_control_lifting :: "('s, 'a, 'b :: Pord) lifting \<Rightarrow>
                                  ('s, 'a, ('x, 'b) control) lifting" where
"no_control_lifting l =
  schem_lift NC (SP NX (SP NX (SINJ l NC)))"

definition no_control_l :: "('s, 'a, 'b :: Pord) lifting \<Rightarrow>
('s \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 
('s \<Rightarrow> ('x, 'b ) control \<Rightarrow> ('x, 'b ) control)" where
"no_control_l l f =
  lift_map_s id (no_control_lifting l) f"

lemma No_Control_LOut :
  shows "LOut (no_control_lifting l) = (\<lambda> s x . LOut l s (payload x))"
  by(cases l; auto simp add:
      no_control_lifting_def schem_lift_defs snd_l_def snd_def)


value [nbe] no_control_lifting

(*
 * assumes Horth : "l_ortho (no_control_l sem) (seq_sem_l_gen lfts)"
 * assumes Hsup : "sups_pres {(no_control_l sem), (seq_sem_l_gen lfts)}"
 * assumes Hf' : "f' = (pcomps [no_control_l sem, seq_sem_l_gen lfts])"
 *)
(* need to remap seq_syn
 * new syntax (?): 2 cases. seq and "other" ('a) *)

(* OK, we need to say something more about the
 * 
 *)
(*
lemma No_Control_Seq_Ortho :
  assumes H: "lifting_validb l S"
  shows "l_ortho (no_control_lifting l) (l_synt (t :: 'a \<Rightarrow> Seq.syn) seq_sem_lifting_gen)"
proof
  fix s a1 a2 b
  show "LUpd (no_control_lifting l) s a1 (LUpd (l_synt t seq_sem_lifting_gen) s a2 b) =
       LUpd (l_synt t seq_sem_lifting_gen) s a2 (LUpd (no_control_lifting l) s a1 b)"
    by(simp add: no_control_lifting_def l_synt_def schem_lift_defs snd_l_def id_l_def fst_l_def seq_sem_lifting_gen_def
        split:prod.splits)
next
  fix s
  show "LBase (no_control_lifting l) s = LBase (l_synt t seq_sem_lifting_gen) s"
    using lifting_validbDB[OF H]
    by(simp add: no_control_lifting_def l_synt_def schem_lift_defs snd_l_def id_l_def fst_l_def seq_sem_lifting_gen_def
        prio_l_def option_l_def prio_bot option_bot prod_bot
        split:prod.splits)
qed
*)

(* OK, we now either need a way to synthesize valid liftings (w/ valid sets)
 * or something else *)
lemma HNo_Control_Seq :
  assumes Valid : "lifting_valid l S"
  assumes Hf' : "f' = (pcomps [no_control_l l sem, seq_sem_l_gen lfts])"
(*  assumes Hsup : "sups_pres {(no_control_l l sem), (seq_sem_l_gen lfts)}" *)
  assumes Hnotseq : "lfts c \<noteq> Sseq"
  assumes H: "sem % {{P1}} c {{P2}}"
  assumes H0 : "gs = pcomps fs"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hnemp : "g \<in> set fs"
  assumes Hdom : "(f' \<down> (set fs) c)"
  shows "|gs| {~ lift_pred_valid_s id l S c P1 ~} [G c z] {~ lift_pred_valid_s id l S c P2 ~}"
proof(rule HT'I)
  fix npost

  have Conc' : "|#gs#| {#-lift_pred_valid_s id l S c P1, (0 + npost)-#} [G c z] 
                       {#-lift_pred_valid_s id l S c P2, npost-#}"
    unfolding add_0
  proof
    fix c'
    assume Guard : "|#gs#| {#lift_pred_valid_s id l S c P2, npost#} c'"
    show "|#gs#| {#lift_pred_valid_s id l S c P1, npost#} ([G c z] @ c')"
    proof
      fix m :: "('a, 'c) control"
      assume HP1 : "lift_pred_valid_s id l S c P1 (payload m)"

      hence HP1' : "P1 (LOut l (c) (payload m))"
        unfolding lift_pred_valid_s_def lift_pred_s_def
        by simp

      have HP1_valid : "payload m \<in> S c"
        using HP1
        unfolding lift_pred_valid_s_def lift_pred_s_def
        by simp

      assume Cont : "cont m = Inl ([G c z] @ c')"

      have HP2 : "P2 (sem c (LOut l c (payload m)))"
        using HTSE[OF H HP1'] by simp

      show "safe_for gs m npost"
      proof(cases "sem_step gs m")
        case (Inr bad)
        then have False using Cont H0
          by(auto simp add: sem_step_def)
  
        then show ?thesis by auto
      next
        case (Inl m')

        have F_eq : "sem_step f' m = Inl m'"
          using sym[OF dominant_pcomps[OF Hpres Hnemp Hdom]] Inl Cont H0
          by(simp add: sem_step_def)

        have Fcont : "cont m' = Inl (c')"
          using Hf' F_eq Cont Hnotseq
            (* TODO: better automation here *)
          by(cases m;cases "lfts c"; auto simp add: schem_lift_defs sem_step_def seq_sem_l_gen_def seq_semx_def seq_sem_def cont_def seq_sem_lifting_gen_def fst_l_def seq_sem_lifting'_def
              prio_l_def option_l_def triv_l_def 
  no_control_l_def no_control_lifting_def snd_l_def 
  prio_bsup prod_bsup option_bsup leq_refl
  split: md_prio.splits option.splits md_triv.splits list.split_asm)
  
        have Fstate : "payload m' = LUpd l c (sem c (LOut l c (payload m))) (payload m)"
          using Hf' F_eq Cont Hnotseq lifting_validDI[OF Valid HP1_valid] bsup_base_leq2
          by(cases m; cases "lfts c"; auto simp add: schem_lift_defs sem_step_def seq_sem_l_gen_def seq_semx_def seq_sem_def cont_def seq_sem_lifting_gen_def fst_l_def seq_sem_lifting'_def
              prio_l_def option_l_def triv_l_def 
              no_control_l_def no_control_lifting_def snd_l_def 
              prio_bsup prod_bsup option_bsup leq_refl
              split: md_prio.splits option.splits md_triv.splits list.split_asm)
  
  (* something is wrong here - we need either a stronger prpperty about l,
   * or to just assume l is id (but then still need assumption about
   * nullability... *)
  
        have M' :  "lift_pred_valid_s id l S c P2 (payload m')"
          unfolding lift_pred_valid_s_def lift_pred_s_def
          unfolding Fstate
          using HP2 lifting_validDO[OF Valid] lifting_validDP[OF Valid]
          by(cases m; auto)
  
        have Safe' : "safe_for gs m' npost" using guardediD[OF Guard M' Fcont] by auto
  
        have Step : "sem_step_p gs m m'" using Inl
          unfolding sem_step_p_eq
          by auto

        have Conc' : "safe_for gs m (1 + npost)"
          using safe_for_extend[OF Safe' Excp_1[OF Step]]
          by simp

        show ?thesis using safe_for_weaken[OF Conc', of npost]
          by simp
      qed
    qed
  qed

  then show "\<exists>npre.
          |#gs#| {#-lift_pred_valid_s id l S c
                     P1, (npre + npost)-#} [G c z] {#-lift_pred_valid_s id l S c P2, npost-#}"
    by blast
qed

end