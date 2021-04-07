theory Seq
  imports "../Gensyn" "../Gensyn_Descend" "../Mergeable/Mergeable" "../Mergeable/MergeableInstances"
          "../Lifting/LiftUtils" "../Lifting/LiftInstances"
          "../Lifting/AutoLift" "../Semantics/Gensyn_Sem_Small"

begin

datatype syn =
  Sseq
  | Sskip


type_synonym state' = "gensyn_skel * unit gs_result * dir"

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
(*
  Seq will always "catch-and-rethrow" exceptions from below
  
*)
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
                                        None \<Rightarrow> (sk, GRDone, Up cp)
                                        | Some cp' \<Rightarrow> (sk, GRPath cp', Up cp))
                              | Some _ \<Rightarrow> (sk, GRPath (cp @ [1+xcph]), Down))
                | _ \<Rightarrow> (case gensyn_cp_parent sk cp of
                          None \<Rightarrow> (sk, GRDone, Up cp)
                         | Some cp' \<Rightarrow> (sk, GRPath cp', Up cp)))))
  | _ \<Rightarrow> st)"


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

definition seq_path :: "state \<Rightarrow> childpath option" where
"seq_path s =
  (case s of
    (_, (mdp _ (Some (mdt (GRPath p)))), _) \<Rightarrow> Some p
    | _ \<Rightarrow> None)"

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

definition seq_gsem :: "(syn, state) g_sem" where
"seq_gsem \<equiv>
  \<lparr> gs_sem = seq_sem_l
  , gs_getpath = seq_path \<rparr>"

end