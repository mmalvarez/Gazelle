theory PrintCalcSeq
  imports PrintCalc "../MergeSemTc/Seq" "../Semantics/Gensyn_Sem"
begin

type_synonym syn = "Seq.syn + PrintCalc.syn"
type_synonym state = "Seq.state * PrintCalc.state"

definition seq_trans :: "syn \<Rightarrow> Seq.syn" where
"seq_trans s =
  (case s of
  Inl s' \<Rightarrow> s'
  | _ \<Rightarrow> Seq.Snext)"

definition printcalc_trans :: "syn \<Rightarrow> PrintCalc.syn" where
"printcalc_trans s =
  (case s of
    Inr s' \<Rightarrow> s'
   | _ \<Rightarrow> Sskip)"

(* problem: need different lifting behaviors
   depending on whether we are Seq or Other (?) *)

definition seq_sem_l ::
  "syn \<Rightarrow> state \<Rightarrow> state" where
"seq_sem_l =
  lift 
    (fst_l (id_l id)) (Seq.seq_sem_l seq_trans)"
    
definition print_calc_sem_l ::
  "syn \<Rightarrow> state \<Rightarrow> state" where
"print_calc_sem_l =
  lift 
    (snd_l (id_l id)) (pcomp print_calc_lc)"

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

value [simp] "pcomp print_calc_seq_lc (Inl (Sseq))
((Some (mdt (gs_sk prog)), (mdp 0 (Some (mdt (GRPath []))))), (mdp 0 (Some (mdt 2)), Some (mdt [])))"


(* finally, need a way to get the childpath/lifting in and out *)
(* we need a "fanout" lg here.
   idea is that we are copying pieces of the product to first and second components.
    *)
(* problem = reversing fst_lg. i think we composed this wrong. *)
definition sem_final :: "(syn, state) x_sem'" where
"sem_final =
  lg_map2' id
    (prod_fan_lg (lg_reverse (fst_lg (prod_lg (option_lg (triv_lg id_lg))
                             (prio_lg_keep (option_lg (triv_lg (id_lg))))))) id_lg)
    (pcomp print_calc_seq_lc)"

value [simp] "(lg_reverse (fst_lg (prod_lg (option_lg (triv_lg id_lg))
                          (prio_lg_keep (option_lg (triv_lg (id_lg)))))))"

(* TO DOS:
- finish generalizing lifting (and lifting validation) to take syntax
- allow for input/output states to differ (e.g. read only/read-write)
*)


definition gsx :: "syn gensyn \<Rightarrow> childpath \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> state option" where
"gsx =
  gensyn_sem_exec (xsem sem_final)"

value [simp] "gsx prog [] ((Some (mdt (gs_sk prog)), (mdp 0 (Some (mdt (GRPath []))))), (mdp 0 (Some (mdt 2)), Some (mdt []))) 90"
value [simp] "gsx (G (Inl Sseq) []) [] ((Some (mdt (gs_sk prog)), (mdp 0 (Some (mdt (GRPath []))))), (mdp 0 (Some (mdt 2)), Some (mdt []))) 90"

end