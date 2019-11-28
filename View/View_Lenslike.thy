theory View_Lenslike imports View "../Lens/Lens"

begin

locale Lenslike = View_Spec +
  assumes ViewLens : "\<And> (r :: 'b) . \<exists> (d :: 'a) . prj r = Inl d"

begin

fun lproj :: "'b \<Rightarrow> 'a" where
"lproj r =
  (case prj r of
    Inl a \<Rightarrow> a)"

abbreviation lp :: "('a, 'b) lens_parms" where
"lp \<equiv> \<lparr> upd = inj
      , proj = lproj
      , vwb = {b . True} \<rparr>"
end

sublocale Lenslike \<subseteq> Lens_Spec lp
  apply(unfold_locales)
     apply(auto split: sum.splits)
      apply(drule_tac InjPrj1) apply(simp)

     apply(cut_tac r = "local.inj (a, b)" in ViewLens) apply(clarsimp)

    apply(simp add:PrjInj1)
   apply(cut_tac r = c in ViewLens) apply(clarsimp)

  apply(simp add: InjInj)
  done

(* next question: what do we require for a composed view to be lenslike? *)
locale Comp_Lenslike = LC : View_Comp +
  LL2 : Lenslike "v2 View_Comp_parms"

(* what does it mean to be prismlike?
 does it mean that prj (inj) is always Inl? (if this were true lenses would be prisms, but they aren't)
 does it mean that inj always ignores its c parameter? this seems better
*)

sublocale Comp_Lenslike \<subseteq> Lenslike "LC.vp"
  apply(unfold_locales)
  apply(case_tac "LC.prj r")
   apply(clarsimp)
  apply(frule_tac LC.PrjInj2)
  apply(clarsimp)
  apply(auto split:sum.splits)
   apply(frule_tac LC.V1.PrjInj2) apply(clarsimp)
  apply(frule_tac LC.V2.PrjInj1) apply(clarsimp)

end