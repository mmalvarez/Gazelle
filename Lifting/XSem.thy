theory XSem
imports "../Mergeable/Mergeable" "../Mergeable/MergeableInstances" "../Gensyn" "../Semantics/Gensyn_Sem"
begin

(* provide a more convenient way to interface between modular
   (denotational) semantics and Gazelle's operational semantics. *)

type_synonym ('x, 'mstate) x_sem' =
  "'x \<Rightarrow>
   ((gensyn_skel md_triv * unit gs_result md_triv) * 'mstate) \<Rightarrow>
   ((gensyn_skel md_triv * unit gs_result md_triv) * 'mstate)"

definition xsem :: "('x, 'mstate) x_sem' \<Rightarrow> ('x, 'mstate, unit) x_sem" where
  "xsem f' x t cp m =
    (case f' x ((mdt (gs_sk t), mdt (GRPath cp)), m) of
      ((mdt t', mdt r'), m') \<Rightarrow> (r', m'))"

end