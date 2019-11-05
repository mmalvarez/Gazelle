theory Prod_Merge_Id imports "Lens_Id" "Prod_Merge"

begin

abbreviation prod_merge_id_parms :: "('t, 't, 't) prod_merge_parms" where
  "prod_merge_id_parms \<equiv> 
  \<lparr> lens1 = lens_id_parms :: ('t, 't) lens_parms
   , lens2 = lens_id_parms :: ('t, 't) lens_parms \<rparr>"

locale Prod_Merge_Id_Spec

sublocale Prod_Merge_Id_Spec \<subseteq> Prod_Merge_Spec "prod_merge_id_parms :: ('t, 't, 't) prod_merge_parms"
  apply(simp add:Prod_Merge_Spec_def) apply(safe)
  apply(rule_tac Lens_Id_Itp.Lens_Spec_axioms)
  apply(unfold_locales)
          apply(auto)
  done

interpretation Prod_Merge_Id_Itp : Prod_Merge_Id_Spec
  done



end