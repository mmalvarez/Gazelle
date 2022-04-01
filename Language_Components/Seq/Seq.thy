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
text_raw \<open>%Snippet gazelle__language_components__seq__seq__syn\<close>
datatype syn =
  Sseq
  | Sskip
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet gazelle__language_components__seq__seq__seq_sem\<close>
type_synonym 'x state' = "'x gensyn list"

definition seq_sem :: "syn \<Rightarrow> 'x state' \<Rightarrow> 'x state'" where
"seq_sem x st =
  (case st of [] \<Rightarrow> []
   | (G s l)#t \<Rightarrow>
     (case x of
      Sskip \<Rightarrow> t
      | Sseq \<Rightarrow> l@t))"
text_raw \<open>%EndSnippet\<close>

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

definition seq_sem_lifting_schem1 where
  "seq_sem_lifting_schem1 = NC "

definition seq_sem_lifting_schem2 where
"seq_sem_lifting_schem2 = (SP (SPRI (SO NC)) NX)"

text_raw \<open>%Snippet gazelle__language_components__seq__seq_prio\<close>
fun seq_prio :: "syn \<Rightarrow> nat" where
"seq_prio _ = 2"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet gazelle__language_components__seq__seq_sem_lifting_gen\<close>
definition seq_sem_lifting_gen :: "(syn, 'x state', ('x, 'a :: Pordb) control) lifting"
  where
"seq_sem_lifting_gen = schem_lift
    NC (SP (SPRC seq_prio (SO NC)) NX)"
text_raw \<open>%EndSnippet\<close>

(* alternate definition that doesn't rely on auto lifter *)
definition seq_sem_lifting' :: "(syn, 'x state', 'x state' md_triv option md_prio) lifting"
  where
"seq_sem_lifting' =
  (prio_l (\<lambda> _ . 0) (\<lambda> _ z . 2 + z) (option_l (triv_l)))"

lemma fst_l_S_univ : 
  "(fst_l_S (\<lambda> _ . UNIV)) = (\<lambda> _ . UNIV)"
  unfolding fst_l_S_def
  by(blast)

lemma seq_sem_lifting_gen_valid :
  "lifting_valid_base_ok (seq_sem_lifting_gen :: (syn, 'x state', ('x, _ :: Pordb) control) lifting) 
                  (schem_lift_S seq_sem_lifting_schem1 seq_sem_lifting_schem2)" unfolding seq_sem_lifting_gen_def seq_sem_lifting_schem1_def seq_sem_lifting_schem2_def
  unfolding seq_sem_lifting'_def schem_lift_defs schem_lift_S_defs
  by(fastforce intro: lifting_valid_fast)

lemma seq_sem_lifting_gen_valid' :
  "lifting_valid_ok (seq_sem_lifting_gen :: (syn, 'x state', ('x, _ :: Pordb) control) lifting) 
                  (schem_lift_S seq_sem_lifting_schem1 seq_sem_lifting_schem2)" unfolding seq_sem_lifting_gen_def seq_sem_lifting_schem1_def seq_sem_lifting_schem2_def
  unfolding seq_sem_lifting'_def schem_lift_defs schem_lift_S_defs
  by(fastforce intro: lifting_valid_fast)

text_raw \<open>%Snippet gazelle__language_components__seq__seq__seq_sem_l_gen\<close>
definition seq_sem_l_gen ::
  "('s \<Rightarrow> syn) \<Rightarrow>
   's \<Rightarrow> (('x, 'y :: Pordb) control) \<Rightarrow> (('x, 'y :: Pordb) control)" where
"seq_sem_l_gen lfts =
  lift_map_s lfts
  seq_sem_lifting_gen
  seq_sem"
text_raw \<open>%EndSnippet\<close>

definition seq_semx :: 
"('s \<Rightarrow> syn) \<Rightarrow>
 ('s, 'x, 'z :: Pordb) sem" where
"seq_semx lfts \<equiv> seq_sem_l_gen lfts"

end