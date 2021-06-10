theory Seq 

  imports "../Gensyn" "../Gensyn_Descend" "../Mergeable/Mergeable" "../Mergeable/MergeableInstances"
          "../Lifting/LiftUtils" "../Lifting/LiftInstances"
          "../Lifting/AutoLift" "../Lifting/AutoLiftProof"  "../Hoare/CPS_Hoare" "../Lifting/LangCompFull"
          "Utils"

begin

datatype syn =
  Sseq
  | Sskip


(* TODO: need additional data? (E.g. to capture error cases *)
type_synonym 'x state' = "'x gensyn list"

definition seq_sem :: "syn \<Rightarrow> 'x state' \<Rightarrow> 'x state'" where
"seq_sem x st =
  (case st of [] \<Rightarrow> []
   | (G s l)#t \<Rightarrow>
     (case x of
      Sskip \<Rightarrow> t
      | Sseq \<Rightarrow> l@t))"

type_synonym ('s, 'x) state = 
  "('s, 'x) control"

(* concrete state *)
type_synonym 's cstate = "('s, unit option) state"


(* TODO: make sure there aren't any weird corner cases in how the auto lifter
   interacts with parameterized stuff *)

(* TODO: the lifter seems to be fine with this, but chokes on anything more complicated... *)

definition seq_sem_lifting_gen :: "(syn, 'x state', ('x, 'a :: Pordb) control) lifting"
  where
"seq_sem_lifting_gen = schem_lift
    NC (SP (SPRI (SO NC)) NX) "

(* alternate definition that doesn't rely on auto lifter *)
definition seq_sem_lifting' :: "(syn, 'x state', 'x state' md_triv option md_prio) lifting"
  where
"seq_sem_lifting' =
  (prio_l (\<lambda> _ . 0) (\<lambda> _ z . 1 + z) (option_l (triv_l)))"

lemma fst_l_S_univ : 
  "(fst_l_S (\<lambda> _ . UNIV)) = (\<lambda> _ . UNIV)"
  unfolding fst_l_S_def
  by(blast)

lemma seq_sem_lifting_gen_validb :
  "lifting_validb (seq_sem_lifting_gen :: (syn, 'x state', ('x, _ :: Pordb) control) lifting) 
                  (\<lambda> _ . UNIV)" unfolding seq_sem_lifting_gen_def
  unfolding seq_sem_lifting'_def schem_lift_defs
  apply(auto intro: lifting_valid lifting_ortho)
  apply(simp only: sym[OF fst_l_S_univ])
  apply(rule fst_l_validb)
  apply(rule prio_l_validb_strong)
    apply(rule option_l_valid_weakb)
    apply(rule triv_l_valid_weak)
   apply(auto)
  done


definition seq_sem_l_gen ::
  "('s \<Rightarrow> syn) \<Rightarrow>
   's \<Rightarrow> (('x, 'y :: Pordb) control) \<Rightarrow> (('x, 'y :: Pordb) control)" where
"seq_sem_l_gen lfts =
  lift_map_s lfts
  seq_sem_lifting_gen
  seq_sem"


definition seq_semx :: 
"('s \<Rightarrow> syn) \<Rightarrow>
 ('s, 'x, 'z :: Pordb) sem" where
"seq_semx lfts \<equiv>
  \<lparr> s_sem = seq_sem_l_gen lfts \<rparr>"


definition prog where
"prog = (G Sseq [G Sseq [], G Sseq []])"

value "sem_exec (seq_semx id) 1 (mdp 0 (Some (mdt [prog])), Some ())"

(* TODO: this proof is currently rather nasty, as it
   involves unfolding a bunch of liftings *)

(* TODO: to use this with other rules, we'll need some notion of monotonicity of
   control flow (i.e. continuation list). perhaps this can be built into
   our Hoare abstraction?
*)
lemma HSeq :
  assumes H0 : "gs = seq_semx lfts"
  assumes H1 : "lfts Sseq' = Sseq"
  assumes H : "|gs| {- P1 -} cs {- P2 -}"
  shows "|gs| {- P1 -} [G Sseq' cs] {- P2 -}"
proof
  fix c'
  assume Safe : "|gs| {P2} c'"

  have Guarded : "|gs| {P1} cs @ c'"
    using HTE[OF H Safe]
    by auto

  show "|gs| {P1} [G Sseq' cs] @ c'"
  proof
    fix m :: "('a, 'b) control"
    assume M : "P1 (snd m)"
    assume CM : "s_cont m = [G Sseq' cs] @ c'"

    show "(safe gs m)"
    proof(cases "(sem_step gs m)")
      case None

      then have False using CM H0
        by(auto simp add: sem_step_def)

      then show ?thesis by auto
    next
      case (Some m')

(*TODO: make this less bad *)
      have CM1 :  "s_cont m' = cs @ c'"
        using Some CM H0 H1
        by(cases m; cases m'; auto simp add: schem_lift_defs sem_step_def seq_semx_def seq_sem_l_gen_def seq_sem_def s_cont_def seq_sem_lifting_gen_def fst_l_def
            prio_l_def option_l_def triv_l_def split: md_prio.splits option.splits md_triv.splits)

(*TODO: make this less bad *)
      have M1_eq : "snd m' = snd m"
        using Some H0
        by(cases m; cases m'; auto simp add: schem_lift_defs sem_step_def seq_semx_def seq_sem_l_gen_def seq_sem_def s_cont_def seq_sem_lifting_gen_def fst_l_def
            prio_l_def option_l_def triv_l_def split: md_prio.splits option.splits md_triv.splits list.split_asm)

      have M1 : "P1 (snd m')" using M unfolding M1_eq by auto

      have Step : "sem_step_p gs m m'"
        using sem_step_sem_step_p[OF Some] by auto

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


(* TODO: do we need the assumption that
fs is nonempty? *)
lemma HSeq_gen :
  assumes H0 : "gs = \<lparr> s_sem = pcomps' fs \<rparr>"
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

  have Guarded : "|gs| {P1} cs @ c'"
    using HTE[OF H Guard]
    by auto

  show "|gs| {P1} [G Sseq' cs] @ c'"
  proof
    fix m :: "('a, 'b) control"
    assume M : "P1 (snd m)"
    assume CM : "s_cont m = [G Sseq' cs] @ c'"

    show "(safe gs m)"
    proof(cases "(sem_step gs m)")
      case None

      then have False using CM H0
        by(auto simp add: sem_step_def)

      then show ?thesis by auto
    next
      case (Some m')

      have F_eq : "sem_step \<lparr> s_sem = f \<rparr> m = Some m'"
        using sym[OF dominant_pcomps'[OF Hpres Hnemp Hdom]] CM Some H0
        by(simp add: sem_step_def)

      have Fcont : "s_cont m' = cs @ c'"
        using HF F_eq CM H2
(* TODO: lifting automation here *)
        apply(cases m; cases m'; auto simp add: schem_lift_defs sem_step_def seq_sem_l_gen_def sem_step_def seq_semx_def seq_sem_l_gen_def seq_sem_def s_cont_def seq_sem_lifting_gen_def fst_l_def seq_sem_lifting'_def
            prio_l_def option_l_def triv_l_def split: md_prio.splits option.splits md_triv.splits list.split_asm)
        done

      have Fstate : "snd m' = snd m"
        using HF F_eq CM H2
        by(cases m; cases m'; auto simp add: schem_lift_defs sem_step_def seq_sem_l_gen_def sem_step_def seq_semx_def seq_sem_l_gen_def seq_sem_def s_cont_def seq_sem_lifting_gen_def fst_l_def seq_sem_lifting'_def
            prio_l_def option_l_def triv_l_def split: md_prio.splits option.splits md_triv.splits list.split_asm)

      hence M' :  "P1 (snd m')" using M unfolding Fstate by auto

      have Safe' : "safe gs m'" using guardedD[OF Guarded M' Fcont] by auto

      have Step : "sem_step_p gs m m'" using Some
        unfolding sem_step_p_eq
        by auto

(* should be easy from this point: just compose executions *)
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
            using Some 
            unfolding imm_safe_def sem_step_p_eq
            by(auto)
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