theory Seq
  imports "../Gensyn" "../Gensyn_Descend" "../Mergeable/Mergeable" "../Mergeable/MergeableInstances"
          "../Lifting/LiftUtils" "../Lifting/LiftInstances"

begin

datatype syn =
  Sseq
  | Sskip

(* idea: these dir's are really defunctionalized continuations *)
datatype dir =
  Down 
  | Up childpath

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

(* standard: nodes will always try to go to their first child
not sure if this should be handled here or on a per-node basis
for now i'm going to see if i can handle it per-node *)

(*
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
*)

fun getlast :: "'a list \<Rightarrow> 'a option" where
"getlast [] = None"
| "getlast [h] = Some h"
| "getlast (h1#h2#t) = getlast (h2#t)"

(* to be strict, we need to check if the returned CP is a suffix of us. *)
(* TODO: factor out the part about deferring to parent *)
(*
(case gensyn_cp_parent sk cp of
      None \<Rightarrow> (sk, GRDone, Up cp)
      | Some cp' \<Rightarrow> (sk, GRPath cp', Up xcp))
*)
(* TODO: when we "re-throw" exceptions (e.g. in the Sskip case)
   should we use our own path as a parameter to Up? *)
definition seq_sem :: "syn \<Rightarrow> state' \<Rightarrow> state'" where
"seq_sem x st =
(case st of (sk, GRPath cp, d) \<Rightarrow>
  (case x of
    Sskip \<Rightarrow> (case gensyn_cp_parent sk cp of
                    None \<Rightarrow> (sk, GRDone, Up cp)
                    | Some cp' \<Rightarrow> (sk, GRPath cp', Up cp))
    | Sseq \<Rightarrow>
        (case d of
          Down \<Rightarrow>
            (case gensyn_get sk (cp @ [0]) of
             None \<Rightarrow> (sk, GRPath cp, Up cp)
             | Some _ \<Rightarrow> (sk, GRPath (cp @ [0]), Down))
          | Up xcp \<Rightarrow> 
             (case get_suffix cp xcp of
              Some (xcph#xcpt) \<Rightarrow> 
                           (case gensyn_get sk (cp @ [1+xcph]) of
                              None \<Rightarrow> (case gensyn_cp_parent sk cp of
                                        None \<Rightarrow> (sk, GRDone, Up xcp)
                                        | Some cp' \<Rightarrow> (sk, GRPath cp', Up xcp))
                              | Some _ \<Rightarrow> (sk, GRPath (cp @ [1+xcph]), Down))
                | _ \<Rightarrow> (case gensyn_cp_parent sk cp of
                          None \<Rightarrow> (sk, GRDone, Up xcp)
                | Some cp' \<Rightarrow> (sk, GRPath cp', Up xcp)))))
  | _ \<Rightarrow> st)"


type_synonym state = "gensyn_skel md_triv option *
                      unit gs_result md_triv option md_prio *
                      dir md_triv option md_prio"

term "(prod_l (option_l (triv_l (id_l)))
             (prod_l 
              (prio_l_inc (option_l (triv_l (id_l))))
              (prio_l_inc (option_l (triv_l (id_l))))))"

instantiation gensyn :: (Bogus) Bogus begin
definition gensyn_bogus :
"bogus = G bogus []"
instance proof qed
end

instantiation gs_result :: (_) Bogus begin
definition gsx_result_bogus :
"bogus = GRUnhandled"
instance proof qed
end

instantiation dir :: Bogus begin
definition dir_bogus :
"bogus = Down"
instance proof qed
end

definition seq_sem_l :: " syn \<Rightarrow> state \<Rightarrow> state" where
"seq_sem_l  =
  l_map_s id
    (prod_l (option_l (triv_l (id_l)))
             (prod_l 
              (prio_l_inc (option_l (triv_l (id_l))))
              (prio_l_inc (option_l (triv_l (id_l)))))) (seq_sem)"

end