theory Seq
  imports "../Gensyn" "../Gensyn_Descend" "../MergeableTc/Mergeable" "../MergeableTc/MergeableInstances"
          "../Lifting/LiftUtils" "../Lifting/LiftInstances"

begin

datatype syn =
  Sseq
  | Snext

datatype dir =
  Down
  | Up

type_synonym state' = "gensyn_skel * unit gs_result * dir"

(*
definition seq_sem :: "('x \<Rightarrow> syn) \<Rightarrow> 'x \<Rightarrow> state' \<Rightarrow> state'" where
"seq_sem f x st =
(case st of (sk, GRPath cp, d) \<Rightarrow>
  (case d of
    Down \<Rightarrow>    
      (case (f x) of
        Snext \<Rightarrow>
            (case gensyn_cp_next sk cp of
                                None => (sk, GRDone)
                                | Some cp' \<Rightarrow> (sk, GRPath cp'))
        | Sseq \<Rightarrow>
            (case gensyn_get sk (cp @ [0]) of
                     None \<Rightarrow> (case gensyn_cp_next sk cp of
                              None => (sk, GRDone)
                              | Some cp' \<Rightarrow> (sk, GRPath cp'))
                     | Some _ \<Rightarrow> (sk, GRPath (cp @ [0])))))
    | _ \<Rightarrow> st)"
*)

definition seq_sem :: "syn \<Rightarrow> state' \<Rightarrow> state'" where
"seq_sem x st =
(case st of (sk, GRPath cp, d) \<Rightarrow>
  (case x of
    Snext \<Rightarrow>
        (case gensyn_cp_sibling sk cp of
         None => (case gensyn_cp_parent sk cp of
                  None \<Rightarrow> (sk, GRDone, Up)
                  | Some cp' \<Rightarrow> (sk, GRPath cp', Up))
         | Some cp' \<Rightarrow> (sk, GRPath cp', Down))
    | Sseq \<Rightarrow>
        (case d of
          Down \<Rightarrow>
            (case gensyn_get sk (cp @ [0]) of
             None \<Rightarrow> (sk, GRPath cp, Up)
             | Some _ \<Rightarrow> (sk, GRPath (cp @ [0]), Down))
          | Up \<Rightarrow>
            (case gensyn_cp_sibling sk cp of
             None => (case gensyn_cp_parent sk cp of
                      None \<Rightarrow> (sk, GRDone, Up)
                      | Some cp' \<Rightarrow> (sk, GRPath cp', Up))
             | Some cp' \<Rightarrow> (sk, GRPath cp', Down))))
  | _ \<Rightarrow> st)"

(* problem - need to keep "skip" from
   ovewriting the "other" at a higher priority *)
(* we need to generalize our "prio" liftings
   so that they can make different decisions based on syntax *)

(* we may not need to do this yet, but probably will at some point.
   for now we sort of "cheat" around this by combining
   next and seq into one language *)

type_synonym state = "gensyn_skel md_triv option *
                      unit gs_result md_triv option md_prio *
                      dir md_triv option md_prio"

term "(prod_l (option_l (triv_l (id_l)))
             (prod_l 
              (prio_l_inc (option_l (triv_l (id_l))))
              (prio_l_inc (option_l (triv_l (id_l))))))"

definition seq_sem_l :: " syn \<Rightarrow> state \<Rightarrow> state" where
"seq_sem_l  =
  l_map2' id
    (prod_l (option_l (triv_l (id_l)))
             (prod_l 
              (prio_l_inc (option_l (triv_l (id_l))))
              (prio_l_inc (option_l (triv_l (id_l)))))) (seq_sem)"

end