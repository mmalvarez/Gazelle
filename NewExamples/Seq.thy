theory Seq
  imports "../Gensyn" "../Gensyn_Descend" "../Mergeable/Mergeable" "../Mergeable/MergeableInstances"
          "../Lifting/LiftUtils" "../Lifting/LiftInstances"
          "../Lifting/AutoLift" "../Semantics/Gensyn_Sem_Small"

begin

datatype syn =
  Sseq
  | Sskip

(*
type_synonym state' = "gensyn_skel * unit gs_result * dir"
*)

(* TODO: do we want to keep the full tree?
   we somehow need access to the children of the current node.
   So just the label on the node will not do.

   we also need to remember which child of the parent we were.
*)

type_synonym state' = "dir * childpath * rel_update"

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
(* rel_updates here are pointing the opposite direction from what we would think?
or do we need another datatype?

somehow the relationship is reversed here.
*)

(*
  hmm, what if we return a list of relative childpaths corresponding to next nodes to visit?
*)

(* let's make sure this is right:
   - "Down" directed signals don't need to carry origin data
   - "up" directed singals do

i dont think we need get_suffix here anymore.

problem: how do we figure out which child we were on?
*)

definition seq_sem :: "(syn * gensyn_skel) \<Rightarrow> state' \<Rightarrow> state'" where
"seq_sem x st =
(case st of
  (d, cp, upd0) \<Rightarrow>
    (case x of
      (Sskip, _) \<Rightarrow> (Up, [], Parent)
      | (Sseq, sk) \<Rightarrow>
          (case d of
            Down \<Rightarrow>
              (case gensyn_get sk ([0]) of
               None \<Rightarrow> (Up, [], Parent)
               | Some _ \<Rightarrow> (Down, [], Desc [0]))
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
                  | Some cp' \<Rightarrow> (sk, GRPath cp', Up xcp)))))"

type_synonym state = "gensyn_skel md_triv option *
                      unit gs_result md_triv option md_prio *
                      dir md_triv option md_prio"


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

(*
definition seq_sem_l :: " syn \<Rightarrow> state \<Rightarrow> state" where
"seq_sem_l  =
  l_map_s id
    (prod_l (option_l (triv_l (id_l)))
             (prod_l 
              (prio_l_inc (option_l (triv_l (id_l))))
              (prio_l_inc (option_l (triv_l (id_l)))))) (seq_sem)"
*)


term "(schem_lift
    (SP NA (SP NB NC)) (SP (SO NA) (SP (SPRI (SO NB)) (SPRI (SO NC)))))"

definition seq_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"seq_sem_l =
  lift_map_s id
  (schem_lift
    (SP NA (SP NB NC)) (SP (SO NA) (SP (SPRI (SO NB)) (SPRI (SO NC)))))
  seq_sem"

end