theory AutoLiftProof
imports LiftUtils LiftInstances AutoLift
begin

(* idea: we want to have automation for
   - validity of liftings
   - orthogonality of merges

  hopefully we can just get away with an intros: set
*)

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
  schem_lift_oalist_recR_def
  schem_lift_fan_recR_def

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
  prio_l_valid_strong
  prio_l_valid_weakb
  prio_l_validb
  prio_l_validb_strong

  fst_l_valid_weak
  fst_l_valid
  fst_l_valid_weakb
  fst_l_validb

  snd_l_valid_weak
  snd_l_valid
  snd_l_valid_weakb
  snd_l_validb

  merge_l_valid

lemmas lifting_valid_vsg =
  id_l_valid_weak_vsg

  triv_l_valid_weak_vsg

  option_l_valid_weak_vsg
  option_l_valid_vsg
  option_l_valid_weakb_vsg
  option_l_validb_vsg
(*
  inl_l_valid_weak_vsg
  inl_l_valid_vsg

  inr_l_valid_weak_vsg
  inr_l_valid
*)
  prio_l_valid_weak_vsg
  prio_l_valid_vsg
  prio_l_valid_strong_vsg
  prio_l_valid_weakb_vsg
  prio_l_validb_vsg
  prio_l_validb_strong_vsg

  fst_l_valid_weak_vsg
  fst_l_valid_vsg
  fst_l_valid_weakb_vsg
  fst_l_validb_vsg

  snd_l_valid_weak_vsg
  snd_l_valid_vsg
  snd_l_valid_weakb_vsg
  snd_l_validb_vsg

  merge_l_valid_vsg


lemmas lifting_valid_vsg' =
  id_l_valid_weak_vsg'

  triv_l_valid_weak_vsg'

  option_l_valid_weak_vsg
  option_l_valid_vsg
  option_l_valid_weakb_vsg
  option_l_validb_vsg
(*
  inl_l_valid_weak_vsg
  inl_l_valid_vsg

  inr_l_valid_weak_vsg
  inr_l_valid
*)
  prio_l_valid_weak_vsg
  prio_l_valid_vsg
  prio_l_valid_strong_vsg'
  prio_l_valid_weakb_vsg
  prio_l_validb_vsg
  prio_l_validb_strong_vsg'

  fst_l_valid_weak_vsg
  fst_l_valid_vsg
  fst_l_valid_weakb_vsg
  fst_l_validb_vsg

  snd_l_valid_weak_vsg
  snd_l_valid_vsg
  snd_l_valid_weakb_vsg
  snd_l_validb_vsg

  merge_l_valid_vsg


lemmas lifting_valid_set_defs =
  option_l_S_def
  prio_l_S_def
  inl_l_S_def
  inr_l_S_def
  fst_l_S_def
  snd_l_S_def

(* TODO: separate out ortho lemmas or no? *)
lemmas lifting_ortho =
  option_ortho
  (* TODO: prio_ortho, option_ortho *)
  fst_snd_ortho
  snd_fst_ortho
  fst_ortho
  snd_ortho

  

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
(*
  apply(auto intro: lifting_valid)
  apply(rule exI)

  apply(rule merge_l_valid)
     apply(force intro: lifting_valid lifting_ortho)
    apply(force intro: lifting_valid lifting_ortho)

  apply(fastforce intro: lifting_valid lifting_ortho)

     apply(rule fst_l_valid)
  apply(rule prio_l_valid_strong)
      apply(auto intro: lifting_valid_vsg simp add: fst_snd_univ)

   apply(rule snd_l_valid)

   apply(rule prio_l_valid_strong)
    apply(auto intro: lifting_valid_vsg simp add: fst_snd_univ)
  apply(rule fst_snd_ortho)
  apply(rule prio_l_validb_strong)
  apply(auto)
   apply(blast intro: lifting_valid)
     apply(force intro: lifting_valid)
  apply(rule prio_l_validb_strong)
     apply(auto intro: lifting_valid)

  apply(unfold lifting_valid_set_defs)
  apply(rule snd_l_valid)
*)
end