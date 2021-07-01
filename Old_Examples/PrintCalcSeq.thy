theory PrintCalcSeq
  imports PrintCalc "Seq" "../Semantics/Gensyn_Sem" "../Lifting/LangComp"
begin

type_synonym syn = "Seq.syn + PrintCalc.syn"
type_synonym state = "Seq.state * PrintCalc.state"

definition seq_trans :: "syn \<Rightarrow> Seq.syn" where
"seq_trans s =
  (case s of
  Inl s' \<Rightarrow> s'
  | _ \<Rightarrow> Seq.Sskip)"

definition printcalc_trans :: "syn \<Rightarrow> PrintCalc.syn" where
"printcalc_trans s =
  (case s of
    Inr s' \<Rightarrow> s'
   | _ \<Rightarrow> PrintCalc.Sskip)"

(* problem: need different lifting behaviors
   depending on whether we are Seq or Other (?) *)

definition seq_sem_l ::
  "syn \<Rightarrow> state \<Rightarrow> state" where
"seq_sem_l =
  lift_map_s seq_trans
    (schem_lift NA (SP (SID NA) NX))
    (Seq.seq_sem_l)"
    
definition print_calc_sem_l ::
  "syn \<Rightarrow> state \<Rightarrow> state" where
"print_calc_sem_l =
  lift_map_s printcalc_trans
    (schem_lift NA (SP NX (SID NA)))
    (pcomp print_calc_lc)"

definition print_calc_seq_lc :: "(syn, state) langcomp" where
"print_calc_seq_lc =
  \<lparr> Sem1 = seq_sem_l
  , Sem2 = print_calc_sem_l \<rparr>"

definition prog :: "syn gensyn" where
"prog =
  G (Inl Sseq) [
    G (Inr (Sreset 0)) [],
    G (Inr (Sadd 2)) [],
    G (Inr (Sadd 3)) [] ]"

definition prog' :: "syn gensyn" where
"prog' =
  G (Inl Sseq) [
    G (Inr (Sreset 0)) [],
    G (Inl Sseq) [G (Inr (Sadd 2)) []],
    G (Inr (Sadd 3)) [] ]"

(*
definition sem_final :: "(syn, state) x_sem'" where
"sem_final =
  l_map_s id
    (schem_lift
      NA (SFAN (l_reverse (schem_lift (SP NA NB) (SP (SOT NA) (SP (SPRK (SOT NB)) NX)))) NA))
    (pcomp print_calc_seq_lc)"
*)
definition sem_final :: "(syn, state) x_sem'" where
"sem_final =
  lift_map_s id
    (schem_lift
      NA (SFAN (l_reverse 
                (schem_lift (SP NA NB) (SP (SP (SO NA) (SP (SPRK (SO NB)) NX)) NX))) 
          NA))
    (pcomp print_calc_seq_lc)"

(* TO DOS:
- finish generalizing lifting (and lifting validation) to take syntax
- allow for input/output states to differ (e.g. read only/read-write)
*)


definition gsx :: "syn gensyn \<Rightarrow> childpath \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> state option" where
"gsx =
  gensyn_sem_exec (xsem sem_final)"

value  "gsx prog' [] ((Some (mdt (gs_sk prog')), (mdp 0 (Some (mdt (GRPath [])))), mdp 0 (Some (mdt Down))), (mdp 0 (Some (mdt 2)), (mdp 0 (Some (mdt []))))) 900"


(*
value  "gsx prog [] ((Some (mdt (gs_sk prog)), (mdp 0 (Some (mdt (GRPath [])))), mdp 0 (Some (mdt Down))), (mdp 0 (Some (mdt 2)), Some (mdt []))) 90"

value  "gsx prog' [] ((Some (mdt (gs_sk prog')), (mdp 0 (Some (mdt (GRPath [])))), mdp 0 (Some (mdt Down))), (mdp 0 (Some (mdt 2)), Some (mdt []))) 900"
*)

end