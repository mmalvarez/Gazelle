theory Seq 

  imports "../Gensyn" "../Gensyn_Descend" "../Mergeable/Mergeable" "../Mergeable/MergeableInstances"
          "../Lifting/LiftUtils" "../Lifting/LiftInstances"
          "../Lifting/AutoLift" "../Hoare/CPS_Hoare"
          "Utils"

begin

datatype syn =
  Sseq
  | Sskip

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


definition seq_sem :: "(syn, 'x state) sem" where
"seq_sem \<equiv>
  \<lparr> s_sem = seq_sem_l
  , s_cont = 
    LOut (seq_sem_lifting) Sseq \<rparr>"

end