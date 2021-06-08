theory ImpCtl
  imports "../Gensyn" "../Gensyn_Descend" "../Mergeable/Mergeable" "../Mergeable/MergeableInstances"
          "../Lifting/LiftUtils" "../Lifting/LiftInstances"
          "../Lifting/AutoLift" "../Hoare/CPS_Hoare" "../Lifting/LangCompFull"
          "Utils"
          "./Seq"
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

type_synonym 'x state' = "'x gensyn list * bool * int"

(* TODO: finish while case *)
(* TODO: error? *)
(*
while ==
- push condition
- push while [body]
- push while [cond, body]
*)
definition imp_ctl_sem :: "syn' \<Rightarrow> 'x state' \<Rightarrow> 'x state'" where
"imp_ctl_sem x st =
  (case st of
    ([], b, i) \<Rightarrow> ([], b, i)
    | ((G z l)#t, b, i) \<Rightarrow>
      ((case x of
        Sskip \<Rightarrow> t
        | Sif \<Rightarrow>
        (case l of
          [body] \<Rightarrow> (if b then body#t else t)
          | [cond, body] \<Rightarrow> cond# ((G z [body])#t)
          | _ \<Rightarrow> [] \<comment>\<open> error \<close>)
        | Swhile \<Rightarrow>
        (case l of
         [body] \<Rightarrow> (if b then body # (G z l) # t else t)
         | [cond, body] \<Rightarrow> cond # (G z [body]) # t
         | _ \<Rightarrow> [] \<comment> \<open> error \<close>))
      , b, i))"

(*
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
*)

datatype syn = 
  Simp syn'
  | Scond cond_syn'
  | Seq "Seq.syn"

type_synonym 'x state = 
  "('x, (bool md_triv option md_prio * int md_triv option md_prio)) control"

definition imp_trans :: "syn \<Rightarrow> syn'" where
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

(*
definition imp_sem_l :: "syn \<Rightarrow> 'x state \<Rightarrow> 'x state" where
"imp_sem_l =
  lift_map_s imp_trans
    (schem_lift (SP (SP NA (SP NB NC)) ND)
                (SP (SP (SO NA) (SP (SPRC imp_prio (SO NB)) (SPRC imp_prio (SO NC))))
                  (SP (SPRK (SO ND)) NX)))
    imp_ctl_sem"
*)

definition imp_sem_l :: "syn \<Rightarrow> 'x state \<Rightarrow> 'x state" where
"imp_sem_l =
  lift_map_s imp_trans
    (schem_lift (SP NA (SP NB NC))
                (SP (SPRC imp_prio (SO NA)) (SP (SPRK (SO NB)) (SPRK (SO NC)))))
  imp_ctl_sem"

(*
definition imp_sem_lifting_gen' :: "(syn, 'x state', ('x, 'y :: Pordb) control) lifting" where
"imp_sem_lifting_gen' = schem_lift
  (SP NA (SP NB NC)) (SP (SPRI (SO NA)) (SP (SPRK (SO NB)) (SPRK (SO (NC)))))"
*)
(* (a, b) control =
  (a gensyn list md_triv option md_prio * b)
*)

(* TODO: it's not letting us name the "extra part at the end" parameter 'y.
but a blank pattern is fine
i don't understand why. 
i'm going to roll with this for now.
*)
definition imp_sem_lifting_gen' :: "(syn', 'x state', 
                                      ('x, bool md_triv option md_prio * 
                                           int md_triv option md_prio * 
                                           (_ :: Pordb)) control) lifting" where
"imp_sem_lifting_gen' = 
 (schem_lift (SP NA (SP NB NC))
                (SP (SPRC imp_prio (SO NA)) (SP (SPRK (SO NB)) (SP (SPRK (SO NC)) NX))))"


term "[imp_sem_lifting_gen', seq_sem_lifting_gen']"

definition seq_sem_l :: "syn \<Rightarrow> 'x state \<Rightarrow> 'x state" where
"seq_sem_l =
  lift_map_s seq_trans
    (schem_lift NA (SP (SPRI (SO NA)) NX))
  seq_sem'"

definition seq_sem_l' :: "syn \<Rightarrow> 'x state \<Rightarrow> 'x state" where
"seq_sem_l' = seq_sem_l_gen seq_trans"

definition sems :: "(syn \<Rightarrow> 'x state \<Rightarrow> 'x state) list" where
"sems = [seq_sem_l', imp_sem_l]"

definition sem_final :: "(syn, 'x, bool md_triv option md_prio * 
                                           int md_triv option md_prio) sem" where
"sem_final = \<lparr> s_sem = (pcomps' sems) \<rparr>"

definition prog where
"prog = (G (Seq Sseq) [(G (Seq Sseq) []), 
                        (G (Simp Sif) [(G (Seq Sseq) []), (G (Seq Sseq) [])])])"

value "sem_exec (sem_final) 4 (mdp 0 (Some (mdt [prog])), (mdp 0 (Some (mdt False))))"

value "sem_exec (sem_final) 5 (mdp 0 (Some (mdt [prog])), (mdp 0 (Some (mdt False))))"


(* next: generalized version of If, While rules*)
(* hmm... need to rephrase in terms of seq_sem_l_gen? *)
(* also, we probably need to have a way to say that
   boolean expressions can't affect control flow (also in terms of domination?)
*)
lemma HImp_gen :
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


end