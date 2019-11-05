theory Lens_Id imports "Lens"

begin

(* locale or interpretation? *)

abbreviation lens_id_parms :: "('a, 'a) lens_parms" where
"lens_id_parms \<equiv> \<lparr> upd = fst
                                , proj = id \<rparr>"

locale Lens_Id_Spec

sublocale Lens_Id_Spec \<subseteq> Lens_Spec "lens_id_parms :: ('t, 't) lens_parms"
 apply(unfold_locales)
    apply(auto)
  done

interpretation Lens_Id_Itp : Lens_Id_Spec 
  done


(*
interpretation Lens_Id : Lens "\<lparr> upd = (\<lambda> x . fst x)
                                , proj = id \<rparr>"
  done
*)


(*
interpretation Lens_Id_Spec : Lens_Spec "lens_id_parms"
  apply(unfold_locales)
    apply(auto)
  done
*)


end