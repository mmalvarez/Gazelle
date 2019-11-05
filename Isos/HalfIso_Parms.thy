theory HalfIso imports Iso
begin

record ('more, 'less) HalfIso_C_Weak_parm =
  forget :: "'more \<Rightarrow> 'less"
  conc :: "'less \<Rightarrow> 'more"

(*declare "HalfIso_C_Weak_parm.defs" [simp]*)

locale HalfIso_C_Weak =
  fixes parm :: "('more, 'less) HalfIso_C_Weak_parm"
begin

abbreviation forget :: "'more \<Rightarrow> 'less" where "forget = HalfIso_C_Weak_parm.forget parm"
abbreviation conc :: "'less \<Rightarrow> 'more" where "conc = HalfIso_C_Weak_parm.conc parm"

end

locale HalfIso_C_Weak_Spec =
  HalfIso_C_Weak +
  assumes Hhisol : "\<And> less . forget (conc less) = less"

record ('more, 'less) HalfIso_parm =
  forget :: "'more \<Rightarrow> 'less"
  conc :: "'less \<Rightarrow> 'more set"


locale HalfIso =
  fixes parm :: "('more, 'less) HalfIso_parm"

begin

definition forget :: "'more \<Rightarrow> 'less" where "forget = HalfIso_parm.forget parm"
definition conc :: "'less \<Rightarrow> 'more set" where "conc = HalfIso_parm.conc parm"

declare forget_def [simp]
declare conc_def [simp]
declare HalfIso_parm.defs [simp]

end



locale HalfIso_Spec = HalfIso +
  assumes Hhisol : "\<And> less . Set.image forget (conc less) = {less}"
  assumes Hhisor : "\<And> more . more \<in> conc (forget more)"

locale HalfIso_C =
  fixes parm :: "('more, 'less) HalfIso_C_Weak_parm"
begin 

definition forget :: "'more \<Rightarrow> 'less" where "forget = HalfIso_C_Weak_parm.forget parm"
definition conc :: "'less \<Rightarrow> 'more" where "conc = HalfIso_C_Weak_parm.conc parm"

definition represent :: "'more \<Rightarrow> 'more set" where
"represent = (\<lambda> more .  {more' . forget more = forget more'})"
end

(*declare HalfIso_C.forget_def [simp]
declare HalfIso_C.conc_def [simp]*)


locale HalfIso_C_Spec = HalfIso_C +
  assumes Hhisol : "\<And> less . forget (conc less) = less"

(* this is kind of annoying... *)

sublocale HalfIso_C_Spec \<subseteq> HI : HalfIso_Spec
  where parm = "HalfIso_parm.make forget (represent o conc)"

(*  rewrites "forget = HalfIso_C_Weak_parm.forget parm" 
  and "conc = HalfIso_C_Weak_parm.conc parm" *)

(*
  where forget = forget
  and conc = "represent o conc"
*)

  apply(unfold_locales) apply(simp)
   apply(auto simp add:represent_def)
    apply(simp add:Hhisol)
   apply(subgoal_tac "less \<in> forget ` {more'. conc less = more'}") 
  apply (simp add:HalfIso.forget_def HalfIso.conc_def HalfIso_parm.defs)
  apply(auto)
   apply(simp add:Hhisol)
  apply (simp add:HalfIso.forget_def HalfIso.conc_def HalfIso_parm.defs)

   apply(simp add:Hhisol) 
  done

sublocale Iso \<subseteq> HalfIso_C
  where forget = to_l
  and conc = to_r
  apply(unfold_locales)
  apply(simp add:Hisol)
  done
   
end