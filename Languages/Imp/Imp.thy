theory Imp
  imports "../../Language_Components/Imp_Ctl/Imp_Ctl" "../../Language_Components/Seq/Seq"
begin

(*
 * A semi-realistic example of putting several components together to make
 * a language.
 * Imp consists of
   * Imp-control
   * Seq
   * Arith
   * Cond
   * Mem
 *)

(* Putting Imp_Ctl together with Cond and
 * Seq to get an IMP-like imperative language.
 *)

(*
definition imp_trans :: "ImpCtl.syn \<Rightarrow> ImpCtl.syn'" where
"imp_trans s =
  (case s of
    Simp s' \<Rightarrow> s'
    | _ \<Rightarrow> Sskip)"

definition cond_trans :: "syn \<Rightarrow> cond_syn'" where
"cond_trans s =
  (case s of
    Scond x \<Rightarrow> x
    | _ \<Rightarrow> Sskip_cond)"

definition seq_trans :: "syn \<Rightarrow> Seq.syn" where
"seq_trans s =
  (case s of
    Seq x \<Rightarrow> x
    | _ \<Rightarrow> Seq.Sskip)"

*)

(* Look in Language_Components attic
 * for the remaining pieces necessary to put this together *)

(*definition seq_sem_l' :: "syn \<Rightarrow> ('x, 'z :: Mergeableb) state \<Rightarrow> ('x, 'z) state" where
"seq_sem_l' = seq_sem_l_gen seq_trans"

definition sems :: "(syn \<Rightarrow> ('x, 'z :: Mergeableb) state \<Rightarrow> ('x, 'z :: Mergeableb) state) list" where
"sems = [seq_sem_l_gen seq_trans, imp_sem_l_gen imp_trans]"

definition sem_final :: "(syn, 'x, bool md_triv option md_prio * 
                                           int md_triv option md_prio
                                    * unit option) sem" where
"sem_final = \<lparr> s_sem = (pcomps' sems) \<rparr>"

definition prog where
"prog = (G (Seq Sseq) [(G (Seq Sseq) []), 
                        (G (Simp Sif) [(G (Seq Sseq) []), (G (Seq Sseq) [])])])"
*)

end