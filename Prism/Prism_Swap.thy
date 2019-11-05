theory Prism_Swap imports Prism
begin

abbreviation prism_swap_parms ::
  "('a + 'b, 'c) prism_parms \<Rightarrow> ('b + 'a, 'c) prism_parms" where
"prism_swap_parms p \<equiv>
  \<lparr> cases =
    (\<lambda> c . case (cases p c) of
            Inl (Inl a) \<Rightarrow> Inl (Inr a)
            | Inl (Inr b) \<Rightarrow> Inl (Inl b)
            | Inr c \<Rightarrow> Inr c)
  , inj = (\<lambda> ba .
    (case ba of
      Inl b \<Rightarrow> inj p (Inr b)
      | Inr a \<Rightarrow> inj p (Inl a))) \<rparr>"

locale Prism_Swap_Spec' =
  fixes Prism_Swap_parms :: "('a + 'b, 'c) prism_parms"

locale Prism_Swap_Spec = Prism_Swap_Spec' +
  P : Prism_Spec "Prism_Swap_parms"

sublocale Prism_Swap_Spec \<subseteq> Prism_Spec "prism_swap_parms Prism_Swap_parms"
  apply(insert P.Prism_Spec_axioms)
  apply(unfold_locales)
  apply(auto split: sum.splits)
             apply(auto simp add:P.Prism_Spec_axioms Prism_Spec_def)
       apply(drule_tac x = c in spec) apply(drule_tac x = c in spec) apply(auto)
      apply(drule_tac x = c in spec) apply(drule_tac x = c in spec) apply(auto)
     apply(drule_tac x = c in spec) apply(drule_tac x = c in spec) apply(auto)
    apply(drule_tac x = c in spec) apply(drule_tac x = c in spec) apply(auto)
   apply(drule_tac x = c in spec) apply(drule_tac x = c in spec) apply(auto)
apply(drule_tac x = c in spec) apply(drule_tac x = c in spec) apply(auto)
  done

end