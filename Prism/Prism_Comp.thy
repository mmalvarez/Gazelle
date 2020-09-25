theory Prism_Comp imports Prism

begin

record ('s1, 'c1, 'c2) prism_comp_parms =
  prism1 :: "('s1, 'c1) prism_parms"
  prism2 :: "('c1, 'c2) prism_parms"

declare prism_comp_parms.defs [simp]

locale Prism_Comp' =
  fixes Prism_Comp_parms :: "('s1, 'c1, 'c2) prism_comp_parms"


locale Prism_Comp = Prism_Comp' +
  P1 : Prism "prism1 Prism_Comp_parms" +
  P2 : Prism "prism2 Prism_Comp_parms"

begin

abbreviation cases1 :: _ where
"cases1 \<equiv> P1.cases"

abbreviation cases2 :: _ where
"cases2 \<equiv> P2.cases"

abbreviation inj1 :: _ where
"inj1 \<equiv> P1.inj"

abbreviation inj2 :: _ where
"inj2 \<equiv> P2.inj"

definition ccases :: "'c \<Rightarrow> ('a + 'c)" where
  "ccases c2 \<equiv> 
    (case (cases2) c2 of
      Inl c1 \<Rightarrow> (case (cases1) c1 of
                   Inl s \<Rightarrow> Inl s
                   | _ \<Rightarrow> Inr c2)
      |  _ \<Rightarrow> Inr c2)"

definition cinj :: "'a \<Rightarrow> 'c" where
  "cinj s1 \<equiv> (inj2) ((inj1) s1)"

abbreviation prism_parms :: "('a, 'c) prism_parms" where
"prism_parms \<equiv> \<lparr> cases = local.ccases
               , inj = local.cinj \<rparr>"

end

locale Prism_Comp_Spec = 
  Prism_Comp +
  PS1 : Prism_Spec "prism1 Prism_Comp_parms" +
  PS2 : Prism_Spec "prism2 Prism_Comp_parms"

sublocale Prism_Comp_Spec \<subseteq> Prism_Spec "prism_parms"
  apply(unfold_locales) apply(simp_all)
    apply(auto simp add: cinj_def ccases_def)
    apply(simp add: PS2.CaseInj) apply(simp add:PS1.CaseInj)

   apply(split sum.split) apply(clarsimp)
  apply(split sum.split) apply(clarsimp) 
   apply(simp add:cinj_def)
  apply(simp add: PS1.CaseInl PS2.CaseInl)

     apply(split sum.split) apply(clarsimp)
  apply(split sum.split) apply(clarsimp) 
  apply(safe) apply(simp add:ccases_def)
  apply(simp add:ccases_def)
  done
end