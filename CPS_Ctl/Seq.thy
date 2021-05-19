theory Seq 

  imports "../Gensyn" "../Gensyn_Descend" "../Mergeable/Mergeable" "../Mergeable/MergeableInstances"
          "../Lifting/LiftUtils" "../Lifting/LiftInstances"
          "../Lifting/AutoLift" "../Hoare/CPS_Hoare"
          "Utils"

begin

datatype syn =
  Sseq
  | Sskip

instantiation syn :: Bogus begin
definition syn_bogus : "bogus = Sskip"
instance proof qed
end

(* TODO: need additional data? (E.g. to capture error cases *)
type_synonym 'x state' = "'x gensyn list"

definition seq_sem' :: "syn \<Rightarrow> 'x state' \<Rightarrow> 'x state'" where
"seq_sem' x st =
  (case st of [] \<Rightarrow> []
   | (G s l)#t \<Rightarrow>
     (case x of
      Sskip \<Rightarrow> t
      | Sseq \<Rightarrow> l@t))"

type_synonym 'x state = "'x gensyn list md_triv option md_prio"

term "(schem_lift
    (SP NA (SP NB NC)) (SP (SO NA) (SP (SPRI (SO NB)) (SPRI (SO NC)))))"


definition seq_sem_lifting :: "(syn, 'x state', 'x state) lifting"
  where
"seq_sem_lifting = schem_lift
    NC (SPRI (SO NC)) "

definition seq_sem_l :: "syn \<Rightarrow> 'x state \<Rightarrow> 'x state" where
"seq_sem_l =
  lift_map_s id
  seq_sem_lifting
  seq_sem'"

definition seq_sem :: "(syn, 'x, 'x state) sem" where
"seq_sem \<equiv>
  \<lparr> s_sem = seq_sem_l
  , s_l = seq_sem_lifting \<rparr>"

definition seq_sem_l_gen ::
  "('s \<Rightarrow> syn) \<Rightarrow>
   (syn, 'x state', ('y :: Pord)) lifting \<Rightarrow>
   's \<Rightarrow> 'y \<Rightarrow> 'y" where
"seq_sem_l_gen lfts lft =
  lift_map_s lfts
  lft
  seq_sem'"

(* TODO: the next thing is making
   sure this all still works in the face of a true merge
   with multiple liftings. *)
definition seq_semx :: 
"('s \<Rightarrow> syn) \<Rightarrow>
 (syn, 'x state', ('y :: Pord)) lifting \<Rightarrow>
 ('s, 'x, ('y :: Pord)) sem" where
"seq_semx lfts lft \<equiv>
  \<lparr> s_sem = seq_sem_l_gen lfts lft
  , s_l = l_synt lfts lft\<rparr>"


(* 
  question
    - is it enough to say "we have a GS that extends Seq"
    - do we need to account for multiple "layers" of composition?

    - if we have a big compound, we would need a bunch of
GS, one for each sub-language
    - type parameter (local syntax) would vary
    - 
*)

lemma HSeq :
  assumes HV : "lifting_valid_weak lft Sv"
  assumes H0 : "gs = seq_semx lfts lft"
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
    fix m
    assume M : "P1 m"
    assume CM : "s_cont gs m = [G Sseq' cs] @ c'"

    obtain m1 where
      Step : "sem_step_p gs m m1" and
      CM1 : "s_cont gs m1 = cs @ c'"
      using CM lifting_valid_weakDO[OF HV] unfolding H0
      apply(simp add: sem_step_p_eq sem_step_def seq_semx_def seq_sem_l_gen_def seq_sem'_def l_synt_def s_cont_def H1)

(* is lifting the right abstraction here?
maybe we actually do want something different.
but, if we can use existing lifting stuff that is a big win
so i'm not ready to give up on using lifting as is, yet. *)

    have M1_eq : "LUpd lft Sseq (cs @ c') m = m1" using Step CM H1 unfolding sem_step_p_eq H0 CM
      by(simp add: sem_step_p_eq sem_step_def seq_semx_def seq_sem_l_gen_def seq_sem'_def split: option.splits list.splits)

    (* need to put entire lifting into definition *)
    have M1 : "P1 m1" sorry

    have Conc' : "safe gs m1" using guardedD[OF Guarded M1 CM1]
      by auto

    show "safe gs m"
    proof
      fix m'
      assume XP : "sem_exec_p gs m m'"
        
      show "imm_safe gs m'" using XP unfolding sem_exec_p_def
      proof(cases rule: rtranclp.cases)
      case rtrancl_refl
        then show ?thesis using imm_safeI_Step[OF Step] by auto
      next
        case RT : (rtrancl_into_rtrancl b)

        have Exc : "sem_exec_p gs m1 m'" unfolding sem_exec_p_def using rtranclp_bisect1[OF sem_step_determ RT(1) Step RT(2)] by auto

        then show ?thesis using safeD[OF Conc' Exc] by auto
      qed
    qed
  qed
qed
end