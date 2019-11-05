theory Sum_Merge_Explicit2 imports "Sum_Merge"
begin

(* the more direct dual of Prod_Merge_Explicit, which I think is unlikely to be useful. *)

abbreviation exp2_prism1_parms :: "('a + 'o, 'a + 'b + 'o) prism_parms" where
"exp2_prism1_parms \<equiv>
  \<lparr> cases = (\<lambda> abo .
    (case abo of Inl a \<Rightarrow> Inl (Inl a)
                | Inr (Inr ov) \<Rightarrow> Inl (Inr ov)
                | _ \<Rightarrow> Inr abo))
  , inj = (\<lambda> ao . case ao of Inl a \<Rightarrow> Inl a
                           | Inr ov \<Rightarrow> Inr (Inr ov)) \<rparr>"

abbreviation exp2_prism2_parms :: "('b + 'o, 'a + 'b + 'o) prism_parms" where
"exp2_prism2_parms \<equiv>
  \<lparr> cases = (\<lambda> abo .
    (case abo of Inr (Inl b) \<Rightarrow> Inl (Inl b)
                | Inr (Inr ov) \<Rightarrow> Inl (Inr ov)
                | _ \<Rightarrow> Inr abo))
  , inj = (\<lambda> bo . case bo of Inl b \<Rightarrow> Inr (Inl b)
                           | Inr ov \<Rightarrow> Inr (Inr ov)) \<rparr>"

abbreviation sum_merge_explicit2_parms ::
  "('a + 'o, 'b + 'o, 'a + 'b + 'o) sum_merge_parms" where
"sum_merge_explicit2_parms \<equiv>
  \<lparr> prism1 = exp2_prism1_parms
  , prism2 = exp2_prism2_parms \<rparr>"

locale Sum_Merge_Explicit2_Spec

sublocale Sum_Merge_Explicit2_Spec \<subseteq> Sum_Merge_Spec "sum_merge_explicit2_parms"
  apply(unfold_locales) apply(auto)
        apply(auto split:sum.splits)
  done

end