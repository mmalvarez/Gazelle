theory Prism_Sums imports "Prism"

begin

abbreviation prism_inl_parms :: "('a, 'a + 'b) prism_parms" where
"prism_inl_parms  \<equiv>
  \<lparr> cases = (\<lambda> ab .
    (case ab of
      Inl a \<Rightarrow> Inl a
      | _ \<Rightarrow> Inr ab))
  , inj = Inl \<rparr>"

locale Prism_Inl_Spec

sublocale Prism_Inl_Spec \<subseteq> Prism_Spec "prism_inl_parms"
  apply(unfold_locales) apply(simp)
   apply(case_tac c, auto)
  apply(case_tac c, auto)
  done

interpretation Prism_Inl_Itp : Prism_Inl_Spec
  done

abbreviation prism_inr_parms :: "('b, 'a + 'b) prism_parms" where
"prism_inr_parms  \<equiv>
  \<lparr> cases = (\<lambda> ab .
    (case ab of
      Inr a \<Rightarrow> Inl a
      | _ \<Rightarrow> Inr ab))
  , inj = Inr \<rparr>"

locale Prism_Inr_Spec

sublocale Prism_Inr_Spec \<subseteq> Prism_Spec "prism_inr_parms"
  apply(unfold_locales) apply(simp)
   apply(case_tac c, auto)
  apply(case_tac c, auto)
  done

interpretation Prism_Inr_Itp : Prism_Inr_Spec
  done

end