theory Auto_Lifter_Proofs_Examples imports Auto_Lifter_Proofs
begin

(*
 * This file contains a few miscellaneous examples of use of the proof infrastructure for the
 * auto-lifter. The proofs here serve as a basic sanity-check on the proof automation.
 *)


value [simp] "schem_lift NA NA"

lemma tlv1 : "lifting_valid_weak (schem_lift NA (SP NX NA)) (\<lambda> _. UNIV)"
  unfolding schem_lift_defs
   by(fastforce simp add: lifting_valid_set_defs intro: lifting_valid_noaxiom )


lemma opt :
  "\<exists> S . lifting_valid_weak_base (schem_lift NA (SO NA)) S"
  unfolding schem_lift_defs
  by(fastforce intro: lifting_valid_noaxiom)

(* could change to: fst_l_S (\<lambda> x . UNIV) = UNIV 
   this will be true for most of the lifting sets (but not all.)*)
lemma fst_snd_univ :
  "fst_l_S (\<lambda> x . UNIV) =
   snd_l_S (\<lambda> x . UNIV)"
  by(auto simp add: fst_l_S_def snd_l_S_def split:prod.splits)

term "(schem_lift NA NA)"

term "(schem_lift (SP NA NB) (SP (SO NA) (SO NB)))"

(* OK. so the automation needs to figure out how to equate some sets of things.
   In principle this should not be very difficult. we just need to
   rephrase the lemmas so that the valid set becomes a variable. *)
lemma mrg :
  "\<exists> S . lifting_valid (schem_lift (SP NA NB) (SP (SPRI (SO NA)) (SPRI (SO NB)))) S"
  unfolding schem_lift_defs     
   by(fastforce intro: lifting_valid_noaxiom_nog lifting_ortho_noaxiom split: soption.splits)

lemma mrg2 :
  obtains Z where
  "lifting_valid (schem_lift (SP NC (SP NB NA)) 
    (SP (SPRI (SO NA)) (SP (SPRI (SO NB)) (SPRI (SO NC))))) Z"
  unfolding schem_lift_defs     
    by(fastforce intro: lifting_valid_noaxiom_nog lifting_ortho_noaxiom_nog split: soption.splits)

lemma mrg2' :
  "lifting_valid (schem_lift (SP NC (SP NB NA)) 
    (SP (SPRI (SO NA)) (SP (SPRI (SO NB)) (SPRI (SO NC)))))
(schem_lift_S (SP NC (SP NB NA)) 
    (SP (SPRI (SO NA)) (SP (SPRI (SO NB)) (SPRI (SO NC))))) "
  unfolding schem_lift_defs schem_lift_S_defs
by(fastforce intro: lifting_valid_noaxiom lifting_ortho_noaxiom)

end