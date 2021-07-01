theory ImpCtl
  imports "../Semantics/Gensyn_Sem" "../Mergeable/MergeableAList"
          "../Mergeable/Mergeable" "../Mergeable/MergeableInstances"
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
(*
definition printcalcseq_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"printcalcseq_sem_l =
  lift_map_s printcalc_trans
     (prod_l id_l (snd_l id_l))
     (pcomp print_calc_seq_lc)"
*)
definition imp_prio :: "(syn' \<Rightarrow> nat)" where
"imp_prio x =
(case x of
    Sskip \<Rightarrow> 0
    | _ \<Rightarrow> 2)"
  
definition imp_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"imp_sem_l =
  lift_map_s imp_trans
    (schem_lift (SP (SP NA (SP NB NC)) ND)
                (SP (SP (SO NA) (SP (SPRC imp_prio (SO NB)) (SPRC imp_prio (SO NC))))
                  (SP (SPRK (SO ND)) NX)))
    imp_ctl_sem"
(*
definition cond_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"cond_sem_l =
  l_map_s cond_trans
    (schem_lift (SP NA NB)
                 (SP NX (SP (SPRI (SOT NA)) (SP (SPRK (SOT NB)) NX))))
  cond_sem"
*)
(*
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
  l_map_s id
    (schem_lift NA
      (SFAN (l_reverse 
                (schem_lift (SP NA NB) (SP (SP (SOT NA) (SP (SPRK (SOT NB)) NX)) NX))) 
          NA))
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
  , (mdp 0 (Some (mdt 2)), (mdp 0 (Some (mdt [])))))"


definition testprog' :: "syn gensyn" where
"testprog' = G (Spc (Inl Sseq)) [G (Spc (Inr (Sreset 0))) []]"


definition initial' :: "state" where
"initial' =
  (  ( Some (mdt (gs_sk testprog'))
     , (mdp 0 (Some (mdt (GRPath []))))
     , mdp 0 (Some (mdt Down)))
  , (mdp 0 (Some (mdt False)))
  , (mdp 0 (Some (mdt 2)), (mdp 0 (Some (mdt [])))))"


value [simp] "(pcomp imp_lc) (Spc (Inl Sseq)) initial'"

value "gsx testprog' [] initial' 20"

value "gsx testprog [] initial 900"

value "gensyn_cp_parent (G () []) []"

definition testprog2 :: "syn gensyn" where
"testprog2 = G (Spc (Inl Sseq))
            [G (Spc (Inr (Sreset 8))) []
            , G (Simp (Swhile))
                [ G (Scond Sgtz) []
                ,  G (Spc (Inr (Ssub 3))) []]]"

value "gsx testprog2 [] initial 900"


declare [[show_types = false]]
(*
lemma what:
  fixes x
  assumes H : "gsx testprog' [] initial' 3 = x"
  shows False using H
  apply(simp add:gsx_def xsem_def testprog'_def initial'_def sem_final_def
        prod_fan_l_def l_reverse_def fst_l_def prod_l_def option_l_def triv_l_def
        l_map_s_def pcomp_def imp_lc_def imp_sem_l_def pcs_cond_lc_def
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
        )
*)
*)
end