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

type_synonym 'x state = 
  "('x, unit option) control"

term "(schem_lift
    (SP NA (SP NB NC)) (SP (SO NA) (SP (SPRI (SO NB)) (SPRI (SO NC)))))"


definition seq_sem_lifting :: "(syn, 'x state', 'x state) lifting"
  where
"seq_sem_lifting = schem_lift
    NC (SP (SPRI (SO NC)) NX) "

definition seq_sem_l :: "syn \<Rightarrow> 'x state \<Rightarrow> 'x state" where
"seq_sem_l =
  lift_map_s id
  seq_sem_lifting
  seq_sem'"

definition seq_sem :: "(syn, 'x, unit option) sem" where
"seq_sem \<equiv>
  \<lparr> s_sem = seq_sem_l \<rparr>"


(* TODO: the next thing is making
   sure this all still works in the face of a true merge
   with multiple liftings. *)
(* TODO: are all these parameters necessary?
   ('s as well as 'x)
*)

(* this isn't quite right. we need to constrain the lifting so that the
   control data is being lifted into the second component *)
(*
definition seq_semx :: 
"('s \<Rightarrow> syn) \<Rightarrow>
 (syn, 'x state', ('x, 'z :: Pord) control) lifting \<Rightarrow>
 ('s, 'x, 'z) sem" where
"seq_semx lfts lft \<equiv>
  \<lparr> s_sem = seq_sem_l_gen lfts lft \<rparr>"
*)


(* TODO: see if there is a way to update the auto lifter so that
   it works with parameterized stuff *)

definition seq_sem_lifting_gen' :: "(syn, 'x state', ('x, 'y :: Pordb) control) lifting"
  where
"seq_sem_lifting_gen' = schem_lift
    NC (SP (SPRI (SO NC)) NX) "

term  "seq_sem_lifting_gen' :: (syn, unit state', (unit, unit option) control) lifting"

definition seq_sem_lifting' :: "(syn, 'x state', 'x state' md_triv option md_prio) lifting"
  where
"seq_sem_lifting' =
  (prio_l (\<lambda> _ . 0) (\<lambda> _ z . 1 + z) (option_l (triv_l)))"

definition seq_sem_lifting_gen :: "(syn, 'x state', ('x, 'y :: Pordb) control) lifting"
  where
"seq_sem_lifting_gen = fst_l (seq_sem_lifting')"

lemma fst_l_S_univ : 
  "(fst_l_S (\<lambda> _ . UNIV)) = (\<lambda> _ . UNIV)"
  unfolding fst_l_S_def
  by(blast)

lemma seq_sem_lifting_gen_validb :
  "lifting_validb (seq_sem_lifting_gen :: (syn, 'x state', ('x, 'y :: Pordb) control) lifting) 
                  (\<lambda> _ . UNIV)" unfolding seq_sem_lifting_gen_def
  unfolding seq_sem_lifting'_def
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
  seq_sem'"


definition seq_semx :: 
"('s \<Rightarrow> syn) \<Rightarrow>
 ('s, 'x, 'z :: Pordb) sem" where
"seq_semx lfts \<equiv>
  \<lparr> s_sem = seq_sem_l_gen lfts \<rparr>"

(* 
  question
    - is it enough to say "we have a GS that extends Seq"
    - do we need to account for multiple "layers" of composition?

    - if we have a big compound, we would need a bunch of
GS, one for each sub-language
    - type parameter (local syntax) would vary
    - 
*)

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
        by(cases m; cases m'; auto simp add: sem_step_def seq_semx_def seq_sem_l_gen_def seq_sem'_def s_cont_def seq_sem_lifting_gen_def fst_l_def seq_sem_lifting'_def
            prio_l_def option_l_def triv_l_def split: md_prio.splits option.splits md_triv.splits)

(*TODO: make this less bad *)
      have M1_eq : "snd m' = snd m"
        using Some H0
        by(cases m; cases m'; auto simp add: sem_step_def seq_semx_def seq_sem_l_gen_def seq_sem'_def s_cont_def seq_sem_lifting_gen_def fst_l_def seq_sem_lifting'_def
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
end