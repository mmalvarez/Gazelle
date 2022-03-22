theory Lifting_Valid_Example
  imports "../Lifter/Auto_Lifter" "../Lifter/Auto_Lifter_Proofs"
begin

text_raw \<open>%Snippet paper_examples__lifting_valid_example__lifting_valid_example\<close>
lemma lifting_valid_example :
  "lifting_valid (schem_lift (SP NC (SP NB NA)) 
    (SP (SPRI (SO NA)) (SP (SPRC (\<lambda> _ . 1) (SO NB)) (SPRI (SO NC)))))
(schem_lift_S (SP NC (SP NB NA)) 
    (SP (SPRI (SO NA)) (SP (SPRC (\<lambda> _ . 1) (SO NB)) (SPRI (SO NC))))) "
  unfolding schem_lift_defs schem_lift_S_defs
  by(fastforce intro: lifting_valid_standard lifting_ortho_standard )
text_raw \<open>%EndSnippet\<close>

end