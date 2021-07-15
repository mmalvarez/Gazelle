theory Seq_Hoare imports 
  Seq "../../Hoare/Hoare" "../../Composition/Composition" "../../Composition/Dominant"
begin

(* Hoare rule for Seq language *)


(* TODO: this proof is currently rather nasty, as it
 * involves unfolding a bunch of liftings. This is an opportunity to improve
 * Auto_Lifter related automation.
 *)

(*
 * Standard Seq Hoare rule. Included mostly for explanatory purposes since it is not able to
 * make any guarantees in the context of Seq merged with other languages - it is "closed"
 * in the sense of requiring a closed world (thus not especially useful).
 * (See HSeq, below).
 *)
lemma HSeq_closed :
  assumes H0 : "gs = seq_semx lfts"
  assumes H1 : "lfts Sseq' = Sseq"
  assumes H : "|gs| {- P1 -} cs {- P2 -}"
  shows "|gs| {- P1 -} [G Sseq' cs] {- P2 -}"
proof
  fix c'
  assume Safe : "|gs| {P2} c'"

  have Guarded : "|gs| {P1} (cs @ c')"
    using HTE[OF H Safe]
    by auto

  show "|gs| {P1} ([G Sseq' cs] @ c')"
  proof
    fix m :: "('a, 'b) control"
    assume M : "P1 (payload m)"
    assume CM : "cont m = Inl ([G Sseq' cs] @ c')"

    show "(safe gs m)"
    proof(cases "(sem_step gs m)")
      case (Inr bad)

      then have False using CM H0
        by(auto simp add: sem_step_def)

      then show ?thesis by auto
    next
      case (Inl m')

(*TODO: make this less bad *)
      have CM1 :  "cont m' = Inl (cs @ c')"
        using Inl CM H0 H1
        by(cases m; auto simp add: schem_lift_defs sem_step_def seq_semx_def seq_sem_l_gen_def seq_sem_def cont_def seq_sem_lifting_gen_def fst_l_def
            prio_l_def option_l_def triv_l_def split: md_prio.splits option.splits md_triv.splits sum.splits)

(*TODO: make this less bad *)
      have M1_eq : "payload m' = payload m"
        using Inl H0
        by(cases m; auto simp add: schem_lift_defs sem_step_def seq_semx_def seq_sem_l_gen_def seq_sem_def cont_def seq_sem_lifting_gen_def fst_l_def
            prio_l_def option_l_def triv_l_def split: md_prio.splits option.splits md_triv.splits list.split_asm)

      have M1 : "P1 (payload m')" using M unfolding M1_eq by auto

      have Step : "sem_step_p gs m m'"
        using sem_step_sem_step_p[OF Inl] by auto

      have Conc' : "safe gs m'" using guardedD[OF Guarded M1 CM1]
        by auto

      show "safe gs m"
      proof
        fix m''
        assume XP : "sem_exec_p gs m m''"
          
        show "imm_safe gs m''" using XP unfolding sem_exec_p_def
        proof(cases rule: rtranclp.cases)
        case rtrancl_refl
          then show ?thesis using imm_safeI_Step[OF Step] by auto
        next
          case RT : (rtrancl_into_rtrancl b)
  
          have Exc : "sem_exec_p gs m' m''" unfolding sem_exec_p_def using rtranclp_bisect1[OF sem_step_determ RT(1) Step RT(2)] by auto
  
          then show ?thesis using safeD[OF Conc' Exc] by auto
        qed
      qed
    qed
  qed
qed

(*
 * More general version of HSeq that applies for any list fs of composed functions meeting
 * certain conditions:
 * - fs is nonempty
 * - fs is dominated by sequence semantics for seq syntax
 *)
(* TODO: do we need the assumption that
fs is nonempty? *)
lemma HSeq_gen :
  assumes H0 : "gs = pcomps fs "
  (*assumes H1 : "seq_sem_l_gen lfts \<in> set fs" *)
  assumes HF : "f = seq_sem_l_gen lfts"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hnemp : "g \<in> set fs"
  assumes Hdom : "(f \<downharpoonleft> (set fs) Sseq')"
  assumes H2 : "lfts Sseq' = Sseq"
  assumes H : "|gs| {- P1 -} cs {- P2 -}"
  shows "|gs| {- P1 -} [G Sseq' cs] {- P2 -}"
proof
  fix c'
  assume Guard : "|gs| {P2} c'"

  have Guarded : "|gs| {P1} (cs @ c')"
    using HTE[OF H Guard]
    by auto

  show "|gs| {P1} ([G Sseq' cs] @ c')"
  proof
    fix m :: "('a, 'b) control"
    assume M : "P1 (payload m)"
    assume CM : "cont m = Inl ([G Sseq' cs] @ c')"

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

      have Fcont : "cont m' = Inl (cs @ c')"
        using HF F_eq CM H2
          (* TODO: better automation here *)
        by(cases m; auto simp add: schem_lift_defs sem_step_def seq_sem_l_gen_def seq_semx_def seq_sem_def cont_def seq_sem_lifting_gen_def fst_l_def seq_sem_lifting'_def
            prio_l_def option_l_def triv_l_def split: md_prio.splits option.splits md_triv.splits list.split_asm)


      have Fstate : "payload m' = payload m"
        using HF F_eq CM H2
        by(cases m; auto simp add: schem_lift_defs sem_step_def seq_sem_l_gen_def seq_semx_def seq_sem_def cont_def seq_sem_lifting_gen_def fst_l_def seq_sem_lifting'_def
            prio_l_def option_l_def triv_l_def split: md_prio.splits option.splits md_triv.splits list.split_asm)

      hence M' :  "P1 (payload m')" using M unfolding Fstate by auto

      have Safe' : "safe gs m'" using guardedD[OF Guarded M' Fcont] by auto

      have Step : "sem_step_p gs m m'" using Inl
        unfolding sem_step_p_eq
        by auto

      show "safe gs m" 
      proof(rule safeI)
        fix m''

        assume Exec : "sem_exec_p gs m m''"
        hence Exec' : "(sem_step_p gs)\<^sup>*\<^sup>* m m''"
          unfolding sem_exec_p_def by auto

        show "imm_safe gs m''" using Exec'
        proof(cases rule: rtranclp.cases)
          case rtrancl_refl
          then show ?thesis 
            using Inl 
            unfolding imm_safe_def sem_step_p_eq
            by(blast)
        next
          case (rtrancl_into_rtrancl b)

          have Exec_final : "sem_exec_p gs m' m''"
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