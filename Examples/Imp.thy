theory Imp
  imports "../MergeSemTc/Seq" "../Semantics/Gensyn_Sem" "../MergeableTc/MergeableAList"
          "../MergeableTc/Mergeable" "../MergeableTc/MergeableInstances"
          "../Lifting/LiftUtils" "../Lifting/LiftInstances" "PrintCalcSeq"
begin

(* conditional/boolean expressions *)
datatype cond_syn' =
  Seqz
  | Sltz
  | Sgtz
  | Sskip_cond

type_synonym cond_state' = "bool * int"

definition cond_sem :: "cond_syn' \<Rightarrow> cond_state' \<Rightarrow> cond_state'" where
"cond_sem x s =
  (case s of (b, i) \<Rightarrow>
    (case x of
      Seqz \<Rightarrow> ((i = 0), i)
      | Sltz \<Rightarrow> ((i < 0), i)
      | Sgtz \<Rightarrow> ((i > 0), i)
      | Sskip_cond \<Rightarrow> s))"

(* Imp control
- IF
- WHILE
- SKIP
*)

datatype syn' =
  Sif
  | Sskip
  | Swhile

(* TODO: fix this so we can actually reassociate, the way you would
   actually want to write it *)
type_synonym state' = "(gensyn_skel * unit gs_result * dir) * bool"

definition imp_ctl_sem :: "syn' \<Rightarrow> state' \<Rightarrow> state'" where
"imp_ctl_sem x st =
  (case st of ((sk, GRPath cp, d), b) \<Rightarrow>
    (case x of
      Sskip \<Rightarrow> st
      | Sif \<Rightarrow> 
        (case d of
         Down \<Rightarrow> ((sk, GRPath (cp @ [0]), Down), b)
         | Up xcp \<Rightarrow>
                 (case get_suffix cp xcp of
                    Some (xcph#xcpt) \<Rightarrow>
                      (case xcph of
                          0 \<Rightarrow> \<comment> \<open>condition\<close>
                            (if b 
                             then ((sk, GRPath (cp @ [1]), Down), b)
                             else ((sk, GRPath (cp @ [2]), Down), b))
                          | _ \<Rightarrow> \<comment> \<open> then/else \<close>
                              (case gensyn_cp_parent sk cp of
                                None \<Rightarrow> ((sk, GRDone, Up cp), b)
                                | Some cp' \<Rightarrow> ((sk, GRPath cp', Up cp), b)))))
        | Swhile \<Rightarrow>
          (case d of
           Down \<Rightarrow> ((sk, GRPath (cp @ [0]), Down), b)
           | Up xcp \<Rightarrow>
                 (case get_suffix cp xcp of
                    Some (xcph#xcpt) \<Rightarrow>
                      (case xcph of
                          0 \<Rightarrow> \<comment> \<open>condition\<close>
                            (if b 
                             then ((sk, GRPath (cp @ [1]), Down), b)
                             else (case gensyn_cp_parent sk cp of
                                     None \<Rightarrow> ((sk, GRDone, Up cp), b)
                                     | Some cp' \<Rightarrow> ((sk, GRPath cp', Up cp), b)))
                          | _ \<Rightarrow> \<comment> \<open> loop body\<close>
                              ((sk, GRPath cp, Down), b))))))"

datatype syn = 
  Spc PrintCalcSeq.syn
  | Simp syn'
  | Scond cond_syn'

type_synonym state = 
  "Seq.state * (bool md_triv option md_prio * PrintCalc.state)"

definition imp_trans :: "syn \<Rightarrow> syn'" where
"imp_trans s =
  (case s of
    Simp s' \<Rightarrow> s'
    | _ \<Rightarrow> Sskip)"

definition printcalc_trans :: "syn \<Rightarrow> PrintCalcSeq.syn" where
"printcalc_trans s =
  (case s of
    Spc x \<Rightarrow> x
    | _ \<Rightarrow> Inl (Seq.Sskip))" (* NB choice of which sskip is arbitrary here *)

definition cond_trans :: "syn \<Rightarrow> cond_syn'" where
"cond_trans s =
  (case s of
    Scond x \<Rightarrow> x
    | _ \<Rightarrow> Sskip_cond)"

term "prod_l (id_l) ((snd_l (snd_l id_l)))"

definition printcalcseq_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"printcalcseq_sem_l =
  l_map2' printcalc_trans
     (prod_l id_l (snd_l id_l))
     (pcomp print_calc_seq_lc)"

definition imp_prio :: "(syn' \<Rightarrow> nat)" where
"imp_prio x =
(case x of
    Sskip \<Rightarrow> 0
    | _ \<Rightarrow> 2)"
  

(* is reassociation going to be a problem? *)
(* also - we need to match on syntax I think?
don't always want inc2 *)
definition imp_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"imp_sem_l =
  l_map2' imp_trans
    (prod_l (prod_l (option_l (triv_l id_l))
                    (prod_l (prio_l_case_inc imp_prio (option_l (triv_l id_l)))
                            (prio_l_case_inc imp_prio (option_l (triv_l id_l)))))
            (fst_l (prio_l_keep (option_l (triv_l id_l)))))
    imp_ctl_sem"

definition cond_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"cond_sem_l =
  l_map2' cond_trans
    (snd_l (prod_l (prio_l_inc (option_l (triv_l id_l))) 
                   (fst_l (prio_l_keep (option_l (triv_l (id_l)))))))
  cond_sem"

definition pcs_cond_lc :: "(syn, state) langcomp" where
"pcs_cond_lc =
  \<lparr> Sem1 = printcalcseq_sem_l
  , Sem2 = cond_sem_l \<rparr>"

definition imp_lc :: "(syn, state) langcomp" where
"imp_lc =
  \<lparr> Sem1 = (pcomp pcs_cond_lc)
  , Sem2 = imp_sem_l \<rparr>"

definition sem_final :: "(syn, state) x_sem'" where
"sem_final =
  l_map2' id
    (prod_fan_l (l_reverse (fst_l (prod_l (option_l (triv_l id_l))
                                          (fst_l (prio_l_keep (option_l (triv_l (id_l)))))))) id_l)
    (pcomp imp_lc)"


definition gsx :: "syn gensyn \<Rightarrow> childpath \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> state option" where
"gsx =
  gensyn_sem_exec (xsem sem_final)"

definition testprog :: "syn gensyn" where 
"testprog = G (Spc (Inl Sseq))
              [ G (Spc (Inr (Sreset 0))) []
              , G (Simp Sif)
                  [ G (Scond Seqz) []
                  , G (Spc (Inr (Sadd 1))) []
                  , G (Spc (Inr (Sadd 2))) [] ]]"

definition initial :: "state" where
"initial =
  (  ( Some (mdt (gs_sk testprog))
     , (mdp 0 (Some (mdt (GRPath []))))
     , mdp 0 (Some (mdt Down)))
  , (mdp 0 (Some (mdt False)))
  , (mdp 0 (Some (mdt 2)), Some (mdt [])))"


definition testprog' :: "syn gensyn" where
"testprog' = G (Spc (Inl Sseq)) [G (Spc (Inr (Sreset 0))) []]"


definition initial' :: "state" where
"initial' =
  (  ( Some (mdt (gs_sk testprog'))
     , (mdp 0 (Some (mdt (GRPath []))))
     , mdp 0 (Some (mdt Down)))
  , (mdp 0 (Some (mdt False)))
  , (mdp 0 (Some (mdt 2)), Some (mdt [])))"

term "(l_reverse (fst_l (prod_l (option_l (triv_l id_l))
                                          (fst_l (prio_l_keep (option_l (triv_l (id_l))))))))"

value [simp] "l_reverse (fst_l (prod_l (option_l (triv_l id_l))
                                          (fst_l (prio_l_keep (option_l (triv_l (id_l)))))))
(Spc (Inl Sseq)) initial'
"


value [simp] "(pcomp imp_lc) (Spc (Inl Sseq)) initial'"

value "gsx testprog' [] initial' 20"

value "gsx testprog [] initial 900"

value "gensyn_cp_parent (G () []) []"

declare [[show_types = false]]

lemma what:
  fixes x
  assumes H : "gsx testprog' [] initial' 3 = x"
  shows False using H
  apply(simp add:gsx_def xsem_def testprog'_def initial'_def sem_final_def
        prod_fan_l_def l_reverse_def fst_l_def prod_l_def option_l_def triv_l_def id_l_def
        l_map2'_def pcomp_def imp_lc_def imp_sem_l_def pcs_cond_lc_def
        printcalcseq_sem_l_def printcalc_trans_def
        print_calc_seq_lc_def imp_ctl_sem_def
        prio_l_keep_def prio_l_inc2_def prio_l_inc_def prio_l_zero_def
        prio_l_def prio_l_const_def
        prod_l_def fst_l_def snd_l_def
        PrintCalcSeq.seq_sem_l_def Seq.seq_sem_l_def
        print_calc_sem_l_def cond_sem_l_def
        print_calc_lc_def
        print_sem_l_def calc_sem_l_def
        imp_trans_def print_trans_def calc_trans_def cond_trans_def seq_trans_def
Imp.printcalc_trans_def)

end