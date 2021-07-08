theory Auto_Lifter_Proofs_Examples imports Auto_Lifter_Proofs
begin

(*
 * This file contains a few miscellaneous examples of use of the proof infrastructure for the
 * auto-lifter. The proofs here serve as a basic sanity-check on the proof automation.
 *)


value [simp] "schem_lift NA NA"

lemma tlv' :
  "lifting_valid_weak' (schem_lift NA NA)"
  unfolding schem_lift_defs
  apply(auto intro: lifting_valid)
  done

lemma opt :
  "\<exists> S . lifting_valid_weakb (schem_lift NA (SO NA)) S"
  unfolding schem_lift_defs
  apply(auto intro: lifting_valid)

  done

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
  by(force intro: lifting_valid lifting_ortho simp add: fst_snd_univ)



end