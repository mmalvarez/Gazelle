theory Imp_Ctl
imports "../../Syntax/Gensyn" "../../Syntax/Gensyn_Descend" "../../Mergeable/Mergeable"
        "../../Mergeable/Mergeable_Instances"
        "../../Lifter/Lifter" "../../Lifter/Lifter_Instances"
        "../../Lifter/Auto_Lifter" "../../Lifter/Auto_Lifter_Proofs" 
        "../../Semantics/Semantics" "../../Composition/Dominant"
        "../Utils"
begin

(*
 * Implementation of standard imperative-language control structures (If and While).
 * These are based off the idealized language IMP (see e.g. _Software Foundations_ vol. 1,, "Imp")
 * and lack constructs such as break and continue. However, the framework is flexible enough
 * to permit description of such constructs and even write Hoare rules for them
 * (for an example of how this might work, see Appel and Blazy,
 * "Separation Logic for Small-Step Cminor")
 *)

(* SWhileC is a while loop in which the condition check is reduced to check of whether
 * a fixed flag (a boolean shared between the cond language state and the
 * imp language state) is true. This makes the Hoare rule somewhat simpler to express.
 *)
datatype syn' =
  Sif
  | Sskip
  | SwhileC

type_synonym 'x imp_state' = "'x gensyn list * int"

definition imp_ctl_sem :: "syn' \<Rightarrow> 'x imp_state' \<Rightarrow> 'x imp_state'" where
"imp_ctl_sem x st =
  (case st of
    ([], b) \<Rightarrow> ([], b)
    | ((G z l)#t, b) \<Rightarrow>
      ((case x of
        Sskip \<Rightarrow> t
        | Sif \<Rightarrow>
        (case l of
          [body] \<Rightarrow> (if (b \<noteq> 0) then body#t else t)
          | [cond, body] \<Rightarrow> cond# ((G z [body])#t)
          | _ \<Rightarrow> [] \<comment>\<open> error \<close>)
        | SwhileC \<Rightarrow>
        (case l of [body] \<Rightarrow> (if (b \<noteq> 0) then body # (G z [body]) # t else t)
         | _ \<Rightarrow> [] \<comment>\<open> error \<close>))
      , b))"


type_synonym ('s, 'x) state = 
  "('s, (int md_triv option md_prio * 'x)) control"

type_synonym ('s) cstate = 
  "('s, unit option) state"



definition imp_prio :: "(syn' \<Rightarrow> nat)" where
"imp_prio x =
(case x of
    Sskip \<Rightarrow> 0
    | _ \<Rightarrow> 2)"


definition imp_sem_lifting_gen :: "(syn', 'x imp_state', 
                                   ('x, _ ) state, _) lifting" where
"imp_sem_lifting_gen = 
 (schem_lift (SP NA NB)
             (SP (SPRC imp_prio (SO NA)) (SP NX (SP (SPRK (SO NB)) NX))))"


definition imp_sem_l_gen :: "('s \<Rightarrow> syn') \<Rightarrow> 's \<Rightarrow> ('x, 'z :: Mergeableb) state \<Rightarrow> ('x, 'z) state" where
"imp_sem_l_gen lfts =
  lift_map_s lfts
    imp_sem_lifting_gen
  imp_ctl_sem"


definition get_cond :: 
"int md_triv option md_prio * 
  (_ :: Pordb) \<Rightarrow> bool option" where
"get_cond st = 
  (case st of
    (b, _) \<Rightarrow> 
    (case b of
      (mdp _ (Some (mdt b'))) \<Rightarrow> Some (if b' = 0 then False else True)
      | _ \<Rightarrow> None))"

end