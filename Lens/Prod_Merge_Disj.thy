theory Prod_Merge_Disj imports "Lens_Pairs" "Prod_Merge"

begin

abbreviation prod_merge_disj_parms :: "('a, 'b, 'a * 'b) prod_merge_parms"
  where
"prod_merge_disj_parms \<equiv> 
  \<lparr> lens1 = lens_fst_parms
  , lens2 = lens_snd_parms \<rparr>"

locale Prod_Merge_Disj_Spec

sublocale Prod_Merge_Disj_Spec \<subseteq> Prod_Merge_Spec "prod_merge_disj_parms"
  apply(simp add:Prod_Merge_Spec_def) apply(safe)
    apply(rule_tac Lens_Fst_Itp.Lens_Spec_axioms)
   apply(rule_tac Lens_Snd_Itp.Lens_Spec_axioms)
  apply(unfold_locales) apply(auto)
  done

interpretation Prod_Merge_Disj_Itp : Prod_Merge_Disj_Spec
  done

end