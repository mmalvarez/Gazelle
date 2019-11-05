theory Sum_Merge_Id imports Sum_Merge Prism_Id

begin


abbreviation sum_merge_id_parms :: "('t, 't, 't) sum_merge_parms" where
"sum_merge_id_parms \<equiv>
  \<lparr> prism1 = prism_id_parms
  , prism2 = prism_id_parms \<rparr>"

locale Sum_Merge_Id_Spec

sublocale Sum_Merge_Id_Spec \<subseteq> Sum_Merge_Spec "sum_merge_id_parms"
  apply(simp add:Sum_Merge_Spec_def) apply(safe)
   apply(rule_tac Prism_Id_Itp.Prism_Spec_axioms)
  apply(unfold_locales, auto)
  done

interpretation Sum_Merge_Id_Itp : Sum_Merge_Id_Spec
  done

end