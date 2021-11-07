theory Seq 

imports "../../Syntax/Gensyn" "../../Syntax/Gensyn_Descend" "../../Mergeable/Mergeable"
        "../../Mergeable/Mergeable_Instances"
        "../../Lifter/Lifter" "../../Lifter/Lifter_Instances"
        "../../Lifter/Auto_Lifter" "../../Lifter/Auto_Lifter_Proofs" 
        "../../Semantics/Semantics" 
        "../Utils"

begin

(*
 * Implementation of sequencing as a language component in Gazelle.
 *)

datatype syn =
  Sseq
  | Sskip

type_synonym 'x state' = "'x gensyn list"

definition seq_sem :: "syn \<Rightarrow> 'x state' \<Rightarrow> 'x state'" where
"seq_sem x st =
  (case st of [] \<Rightarrow> []
   | (G s l)#t \<Rightarrow>
     (case x of
      Sskip \<Rightarrow> t
      | Sseq \<Rightarrow> l@t))"

type_synonym ('s, 'x) state = 
  "('s, 'x) control"

(* concrete state *)
type_synonym 's cstate = "('s, unit option) state"

(* We define a lifting here to show how Seq overlaps with the standard control-flow
 * constructs
 *)

(* TODO: the auto-lifter seems to sometimes struggle a bit when one of the types involved
 * is a type variable (e.g. 'x state'), but it works in this case. Should figure out
 * to what extent this is an issue or just a usability bug (or even just a matter
 * of terrible error messages making it hard to see what's going on) *)

(* TODO: is this the correct priority calculation? *)
definition seq_sem_lifting_gen :: "(syn, 'x state', ('x, 'a :: Pordb) control, _) lifting"
  where
"seq_sem_lifting_gen = schem_lift
    NC (SP (SPRI (SO NC)) NX) "

(* alternate definition that doesn't rely on auto lifter *)
definition seq_sem_lifting' :: "(syn, 'x state', 'x state' md_triv option md_prio, _) lifting"
  where
"seq_sem_lifting' =
  (prio_l (\<lambda> _ . 0) (\<lambda> _ z . 1 + z) (option_l (triv_l)))"

lemma fst_l_S_univ : 
  "(fst_l_S (\<lambda> _ . UNIV)) = (\<lambda> _ . UNIV)"
  unfolding fst_l_S_def
  by(blast)

lemma seq_sem_lifting_gen_validb :
  "lifting_validb (seq_sem_lifting_gen :: (syn, 'x state', ('x, _ :: Pordb) control) lifting) 
                  (\<lambda> _ . UNIV)" unfolding seq_sem_lifting_gen_def
  unfolding seq_sem_lifting'_def schem_lift_defs
  apply(auto intro: lifting_valid lifting_ortho)
  apply(simp only: sym[OF fst_l_S_univ])
  apply(rule fst_l_validb)
  apply(rule prio_l_validb_strong)
    apply(rule option_l_valid_weakb)
    apply(rule triv_l_valid_weak)
   apply(auto)
  done


definition seq_sem_l_gen ::
  "('s \<Rightarrow> syn) \<Rightarrow>
   's \<Rightarrow> (('x, 'y :: Pordb) control) \<Rightarrow> (('x, 'y :: Pordb) control)" where
"seq_sem_l_gen lfts =
  lift_map_s lfts
  seq_sem_lifting_gen
  seq_sem"


definition seq_semx :: 
"('s \<Rightarrow> syn) \<Rightarrow>
 ('s, 'x, 'z :: Pordb) sem" where
"seq_semx lfts \<equiv> seq_sem_l_gen lfts"

end