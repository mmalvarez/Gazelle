theory Auto_Lifter_Proofs
imports Lifter Lifter_Instances Auto_Lifter
begin

(* 
 * In this file, we have some rather basic proof automation (really just lemma-lists to supply
 * to Isabelle's automation) to support reasoning about the output of the schem_lift automation
 * (see Auto_Lifter.thy) without having to manually unfold definitions and dig into the
 * details of what that lifting is actually doing.
 *
 * This file (currently) supports proving
 * various notions of validity (see Lifter.thy) for the liftings 
 * generated by the auto lifter. This tends to be straightforward since the auto lifter
 * is really just composing liftings already known to be valid. However, sometimes the
 * lifting transformers involved have nontrivial side-conditions, which can make the proof
 * more difficult. We aim to at least handle the easy cases effortlessly.
 *
 * One common case where the proof can become a bit more challenging but should still be
 * relatively easy to automate is when the side-condition stipulates that a pair of liftings
 * needs to be orthogonal in order for the lifting to be valid. Such cases can also be automatable
 * if the orthogonality falls directly out of the structure of the liftings involved
 * (e.g. when merging fst_l and snd_l, orthogonality is trivial)
 *)

(* TODO: automation for orthogonality, sups_pres, etc. (side-conditions on when merging
 * two or more semantics is well defined) *)

(* vsg versions add a side condition on equality of the valid set,
   which might make them more useful. *)

lemmas schem_lift_defs =
  schem_lift_base_trivA_def
  schem_lift_base_trivB_def
  schem_lift_base_trivC_def
  schem_lift_base_trivD_def
  schem_lift_base_trivE_def

  schem_lift_base_idA_def
  schem_lift_base_idB_def
  schem_lift_base_idC_def
  schem_lift_base_idD_def
  schem_lift_base_idE_def

  schem_lift_option_recR_def
  schem_lift_prio_recR_def
  (*schem_lift_oalist_recR_def*)
  (*schem_lift_fan_recR_def*)

  schem_lift_prod_recR_A_left_def
  schem_lift_prod_recR_A_right_def
  schem_lift_prod_recR_B_left_def
  schem_lift_prod_recR_B_right_def
  schem_lift_prod_recR_C_left_def
  schem_lift_prod_recR_C_right_def
  schem_lift_prod_recR_D_left_def
  schem_lift_prod_recR_D_right_def
  schem_lift_prod_recR_E_left_def
  schem_lift_prod_recR_E_right_def

  schem_lift_merge_recR_A_left_def
  schem_lift_merge_recR_A_right_def
  schem_lift_merge_recR_B_left_def
  schem_lift_merge_recR_B_right_def
  schem_lift_merge_recR_C_left_def
  schem_lift_merge_recR_C_right_def
  schem_lift_merge_recR_D_left_def
  schem_lift_merge_recR_D_right_def
  schem_lift_merge_recR_E_left_def
  schem_lift_merge_recR_E_right_def

  schem_lift_recL_def
  schem_lift_inject_def

lemmas lifting_defs =
  prio_l_inc_def
  prio_l_inc2_def
  prio_l_incN_def
  prio_l_case_inc_def

lemmas lifting_valid =
  id_l_valid_weak

  triv_l_valid_weak

  option_l_valid_weak
  option_l_valid
  option_l_valid_weakb
  option_l_validb

  inl_l_valid_weak
  inl_l_valid

  inr_l_valid_weak
  inr_l_valid

  prio_l_valid_weak
  prio_l_valid
  (*prio_l_valid_strong*)
  prio_l_valid_stronger
  prio_l_valid_weakb
  prio_l_validb
  (*prio_l_validb_strong*)
  prio_l_validb_stronger
  

  fst_l_valid_weak
  fst_l_valid
  fst_l_valid_weakb
  fst_l_validb

  snd_l_valid_weak
  snd_l_valid
  snd_l_valid_weakb
  snd_l_validb

  (*merge_l_valid*)
  merge_l_valid_gen
merge_l_validb_gen

(* TODO: is this one useful still?
 * i feel like maybe vsg' is overall better.
 *)
lemmas lifting_valid_vsg =
  id_l_valid_weak_vsg

  triv_l_valid_weak_vsg

  option_l_valid_weak_vsg
  option_l_valid_vsg
  option_l_valid_weakb_vsg
  option_l_validb_vsg

(* TODO: add support for sum *)
(*
  inl_l_valid_weak_vsg
  inl_l_valid_vsg

  inr_l_valid_weak_vsg
  inr_l_valid
*)
  prio_l_valid_weak_vsg
  prio_l_valid_vsg
  (*prio_l_valid_strong_vsg*)
  prio_l_valid_stronger
  prio_l_valid_weakb_vsg
  prio_l_validb_vsg
  (*prio_l_validb_strong_vsg*)
  prio_l_validb_stronger

  fst_l_valid_weak_vsg
  fst_l_valid_vsg
  fst_l_valid_weakb_vsg
  fst_l_validb_vsg

  snd_l_valid_weak_vsg
  snd_l_valid_vsg
  snd_l_valid_weakb_vsg
  snd_l_validb_vsg

  merge_l_valid_gen_vsg'
merge_l_validb_gen_vsg'


lemmas lifting_valid_vsg' =
  id_l_valid_weak_vsg'

  triv_l_valid_weak_vsg'

  option_l_valid_weak_vsg
  option_l_valid_vsg
  option_l_valid_weakb_vsg
  option_l_validb_vsg

(* TODO: add support for sum *)

(*
  inl_l_valid_weak_vsg
  inl_l_valid_vsg

  inr_l_valid_weak_vsg
  inr_l_valid
*)
  prio_l_valid_weak_vsg
  prio_l_valid_vsg
  (*prio_l_valid_strong_vsg'*)
prio_l_valid_stronger
  prio_l_valid_weakb_vsg
  prio_l_validb_vsg
(*  prio_l_validb_strong_vsg'*)
prio_l_valid_stronger

  fst_l_valid_weak_vsg
  fst_l_valid_vsg
  fst_l_valid_weakb_vsg
  fst_l_validb_vsg


  snd_l_valid_weak_vsg
  snd_l_valid_vsg
  snd_l_valid_weakb_vsg
  snd_l_validb_vsg

  (*merge_l_valid_vsg*)
merge_l_valid_gen_vsg'
  merge_l_validb_gen_vsg'


lemmas lifting_valid_set_defs =
  option_l_S_def
  prio_l_S_def

  fst_l_S_def
  snd_l_S_def

(* TODO: separate out orthogonality lemmas or no? *)
lemmas lifting_ortho =
  option_ortho
  fst_snd_ortho
  snd_fst_ortho
  fst_ortho
  snd_ortho

lemmas lifting_ortho_alt =
  option_ortho_alt
  fst_snd_ortho_alt
  snd_fst_ortho_alt
  fst_ortho_alt
  snd_ortho_alt


end