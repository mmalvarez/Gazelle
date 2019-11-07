theory Sum_Merge_Disj imports "Prism_Sums" "Sum_Merge"

begin

abbreviation sum_merge_disj_parms ::
  "('a, 'b, 'a + 'b) sum_merge_parms"
  where
  "sum_merge_disj_parms \<equiv>
  \<lparr> prism1 = prism_inl_parms
  , prism2 = prism_inr_parms \<rparr>"

locale Sum_Merge_Disj_Spec

sublocale Sum_Merge_Disj_Spec \<subseteq> Sum_Merge_Spec "sum_merge_disj_parms"
  apply(simp add:Sum_Merge_Spec_def) apply(safe)
  apply(rule_tac Prism_Inl_Itp.Prism_Spec_axioms)
   apply(rule_tac Prism_Inr_Itp.Prism_Spec_axioms)
  apply(unfold_locales, simp)
  apply(case_tac c, auto)
  done

interpretation Sum_Merge_Disj_Itp : Sum_Merge_Disj_Spec
  done
end