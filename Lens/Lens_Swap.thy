theory Lens_Swap imports Lens
begin

(* problem - now we get to a point where we actually
   need functions over lenses. *)

(* prod.swap *)
abbreviation lens_swap_parms ::
  "('a * 'b, 'c) lens_parms \<Rightarrow> ('b * 'a, 'c) lens_parms" where
"lens_swap_parms l \<equiv>
  \<lparr> upd = (\<lambda> abc . (upd l) (prod.swap (fst abc), snd abc))
  , proj = (\<lambda> c . prod.swap (proj l c) )
  , vwb = vwb l \<rparr>"

locale Lens_Swap_Spec' =
  fixes Lens_Swap_parms :: "('a * 'b, 'c) lens_parms"

locale Lens_Swap_Spec = Lens_Swap_Spec' +
  L : Lens_Spec "Lens_Swap_parms"
  

sublocale Lens_Swap_Spec \<subseteq> Lens_Spec "lens_swap_parms Lens_Swap_parms"
  apply(insert L.Lens_Spec_axioms)
  apply(unfold_locales)
  apply(auto)
    apply(auto simp add:L.Lens_Spec_axioms Lens_Spec_def)
  done

end