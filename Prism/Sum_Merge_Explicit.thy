theory Sum_Merge_Explicit imports "Sum_Merge"

begin

abbreviation exp_prism1_parms :: "('a * 'o, ('a + 'b) * 'o) prism_parms" where
"exp_prism1_parms \<equiv>
  \<lparr> cases = (\<lambda> abo . 
    (case abo of (Inl a, ov) \<Rightarrow> Inl (a, ov)
      | _ \<Rightarrow> Inr abo))
  , inj = (\<lambda> ao . case ao of (a, ov) \<Rightarrow> (Inl a, ov)) \<rparr>"

abbreviation exp_prism2_parms :: "('b * 'o, ('a + 'b) * 'o) prism_parms" where
"exp_prism2_parms \<equiv>
  \<lparr> cases = (\<lambda> abo .
    (case abo of (Inr b, ov) \<Rightarrow> Inl (b, ov)
    | _ \<Rightarrow> Inr abo))
  , inj = (\<lambda> bo . case bo of (b, ov) \<Rightarrow> (Inr b, ov)) \<rparr>"

abbreviation sum_merge_explicit_parms :: "('a * 'o, 'b * 'o, ('a + 'b) * 'o) sum_merge_parms" where
"sum_merge_explicit_parms \<equiv>
  \<lparr> prism1 = exp_prism1_parms
  , prism2 = exp_prism2_parms \<rparr>"

locale Sum_Merge_Explicit_Spec

sublocale Sum_Merge_Explicit_Spec \<subseteq> Sum_Merge_Spec "sum_merge_explicit_parms"
  apply(unfold_locales) apply(auto)
      apply(case_tac a, auto)
  apply(case_tac a, auto)
    apply(case_tac a, auto)
   apply(case_tac a, auto)
  done

interpretation Sum_Merge_Explicit_Itp : Sum_Merge_Explicit_Spec
  done
end