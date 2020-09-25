theory Deify imports Main "Lens/Lens" Reify

(* dual of reify, lets us pack objects together into
   one gigantic state that we can lens from *)

begin

(* should everything be optional? *)
(* doing prod/sum is going to be pretty inconvenient.
   perhaps this isn't worth it? *)
record deified =
  DNat :: "nat"
  DUnit :: "unit"
  DBool :: "bool"
  DCalc :: "calc"

class deire =
  fixes deify :: "'a \<Rightarrow> deified \<Rightarrow> deified"
  fixes renote :: "deified \<Rightarrow> 'a"
  fixes inhabitant :: 'a
  assumes HLens : "Lens.Lens_Spec \<lparr> upd = (\<lambda> (a, b) . deify a b)
                                  , proj = renote \<rparr>"

begin

definition proj where
  "proj = (\<lambda> (a, b) . deify a b)"

definition upd where  "upd = renote"

(* lemmata here? *)

end

instantiation nat :: deire
begin
definition ddnat_def : "deify x d = d \<lparr> DNat := x \<rparr>"
definition rrnat_def : "renote d = DNat d"

instance proof
  show "Lens_Spec
     \<lparr>lens_parms.upd = \<lambda>(a, b). deify (a :: nat) b, proj = renote\<rparr>"
    apply(simp add:Lens_Spec_def)
    apply(auto simp add: ddnat_def rrnat_def)
    done
qed

end

instantiation unit :: deire
begin
definition ddunit_def : "deify x d = d \<lparr> DUnit := x \<rparr>"
definition rrunit_def : "renote d = DUnit d"

instance proof
    show "Lens_Spec
     \<lparr>lens_parms.upd = \<lambda>(a, b). deify (a :: unit) b, proj = renote\<rparr>"
    apply(simp add:Lens_Spec_def)
    apply(auto simp add: ddunit_def rrunit_def)
      done
  qed
end

instantiation bool :: deire
begin
definition ddbool_def : "deify x d = d \<lparr> DBool := x \<rparr>"
definition rrbool_def : "renote d = DBool d"

instance proof
    show "Lens_Spec
     \<lparr>lens_parms.upd = \<lambda>(a, b). deify (a :: bool) b, proj = renote\<rparr>"
    apply(simp add:Lens_Spec_def)
    apply(auto simp add: ddbool_def rrbool_def)
      done
  qed
end

instantiation calc :: deire
begin
definition ddcalc_def : "deify x d = d \<lparr> DCalc := x \<rparr>"
definition rrcalc_def : "renote d = DCalc d"

instance proof
    show "Lens_Spec
     \<lparr>lens_parms.upd = \<lambda>(a, b). deify (a :: calc) b, proj = renote\<rparr>"
    apply(simp add:Lens_Spec_def)
    apply(auto simp add: ddcalc_def rrcalc_def)
      done
  qed
end


end