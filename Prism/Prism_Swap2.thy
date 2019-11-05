theory Prism_Swap2 imports Prism

(* swap producted, rather than summed, components of a prism *)

begin

abbreviation prism_swap2_parms ::
  "('a * 'b, 'c) prism_parms \<Rightarrow> ('b * 'a, 'c) prism_parms" where
"prism_swap2_parms p \<equiv>
  \<lparr> cases = (\<lambda> c . case (cases p c) of
       Inl (a, b) \<Rightarrow> Inl (b, a)
       | Inr c \<Rightarrow> Inr c)
  , inj = (\<lambda> ba .
      inj p (prod.swap ba)) \<rparr>"


locale Prism_Swap2_Spec' =
  fixes Prism_Swap2_parms :: "('a * 'b, 'c) prism_parms"

locale Prism_Swap2_Spec = Prism_Swap2_Spec' +
  P : Prism_Spec "Prism_Swap2_parms"

sublocale Prism_Swap2_Spec \<subseteq> Prism_Spec "prism_swap2_parms Prism_Swap2_parms"
  apply(insert P.Prism_Spec_axioms)
  apply(unfold_locales)
    apply(auto simp add:P.Prism_Spec_axioms Prism_Spec_def)
  apply(auto split:sum.splits)
   apply(drule_tac x = c in spec) apply(drule_tac x = c in spec)
     apply(auto)
apply(drule_tac x = c in spec) apply(drule_tac x = c in spec)
    apply(auto)
apply(drule_tac x = c in spec) apply(drule_tac x = c in spec)
   apply(auto)
apply(drule_tac x = c in spec) apply(drule_tac x = c in spec)
  apply(auto)
  done

end