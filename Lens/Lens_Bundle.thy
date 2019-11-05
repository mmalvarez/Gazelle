theory Lens_Bundle imports Lens
begin

abbreviation lens_bundle_parms ::
  "('a, 'x) lens_parms \<Rightarrow> ('b, 'y) lens_parms \<Rightarrow> ('a * 'b, 'x * 'y) lens_parms"
  where
"lens_bundle_parms l1 l2 \<equiv>
  \<lparr> upd = (\<lambda> abxy . case abxy of ((a, b), x, y) \<Rightarrow> ((upd l1) (a, x), (upd l2) (b, y)))
  , proj = ( \<lambda> c . ((proj l1) (fst c), (proj l2) (snd c))) \<rparr>"


locale Lens_Bundle_Spec' =
  fixes Lens_Bundle_parms1 :: "('a, 'x) lens_parms"
  fixes Lens_Bundle_parms2 :: "('b, 'y) lens_parms"

locale Lens_Bundle_Spec = Lens_Bundle_Spec' +
  L1 : Lens_Spec "Lens_Bundle_parms1" +
  L2 : Lens_Spec "Lens_Bundle_parms2"

sublocale Lens_Bundle_Spec \<subseteq> Lens_Spec "lens_bundle_parms Lens_Bundle_parms1 Lens_Bundle_parms2"
  apply(insert L1.Lens_Spec_axioms) apply(insert L2.Lens_Spec_axioms)
  apply(unfold_locales) apply(auto simp add:Lens_Spec_def)
  done

end