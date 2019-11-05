theory Prism_Id imports "Prism"

begin

abbreviation prism_id_parms :: "('a, 'a) prism_parms" where
"prism_id_parms \<equiv> 
  \<lparr> cases = (\<lambda> a . Inl a)
  , inj = id \<rparr>"

locale Prism_Id_Spec

sublocale Prism_Id_Spec \<subseteq> Prism_Spec "prism_id_parms :: ('t, 't) prism_parms"
  apply(unfold_locales) apply(auto)
  done

interpretation Prism_Id_Itp : Prism_Id_Spec
  done

end