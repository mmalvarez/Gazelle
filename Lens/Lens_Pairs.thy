theory Lens_Pairs imports "Lens"

begin

abbreviation lens_fst_parms :: "('a, 'a * 'b) lens_parms" where
"lens_fst_parms \<equiv> \<lparr> upd = (\<lambda> m1c . 
      (case m1c of (m1, c1, c2) \<Rightarrow> (m1, c2)))
      , proj = fst
      , vwb = {(a, b) . True} \<rparr>"

locale Lens_Fst_Spec

sublocale Lens_Fst_Spec \<subseteq> Lens_Spec "lens_fst_parms"
  apply(unfold_locales) apply(auto)
  done

interpretation Lens_Fst_Itp : Lens_Fst_Spec
  done

abbreviation lens_snd_parms :: "('b, 'a * 'b) lens_parms" where
"lens_snd_parms \<equiv> \<lparr> upd = (\<lambda> m2c .
    (case m2c of (m2, c1, c2) \<Rightarrow> (c1, m2)))
    , proj = snd
    , vwb = {(a, b) . True} \<rparr>"

locale Lens_Snd_Spec

sublocale Lens_Snd_Spec \<subseteq> Lens_Spec "lens_snd_parms"
  apply(unfold_locales) apply(auto)
  done

interpretation Lens_Snd_Itp : Lens_Snd_Spec
  done

end