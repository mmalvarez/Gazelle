theory Prod_Merge_Explicit imports "Prod_Merge"

begin

(* idea: this file gives us a fully structured prod_merge.
sometimes this is useful, but ideally we should strive for
lenses requiring less type structure *)

(* idea: bundle two lenses into a single lens
   one lens ('a, 'b) another ('c, 'd) into ('a, 'd) ('b, 'd) *)
(* we also need a "swap" for lenses *)

abbreviation exp_lens1_parms :: "('a * 'o, 'a * 'b * 'o) lens_parms" where
"exp_lens1_parms \<equiv> \<lparr> upd = (\<lambda> aoabo . 
                      (case aoabo of ((a', ov'), (a, b, ov)) \<Rightarrow> (a', b, ov')))
                   , proj = (\<lambda> abo . 
                      (case abo of (a, b, ov) \<Rightarrow> (a, ov))) \<rparr>"

abbreviation exp_lens2_parms :: "('b * 'o, 'a * 'b * 'o) lens_parms" where
"exp_lens2_parms \<equiv> \<lparr> upd = (\<lambda> boabo . (case boabo of ((b', ov'), (a, b, ov)) \<Rightarrow> (a, b', ov')))
                   , proj = (\<lambda> abo . (case abo of (a, b, ov) \<Rightarrow> (b, ov))) \<rparr>"

abbreviation prod_merge_explicit_parms :: "('a * 'o, 'b * 'o, 'a * 'b * 'o) prod_merge_parms" where 
"prod_merge_explicit_parms \<equiv>
  \<lparr> lens1 = exp_lens1_parms
  ,  lens2 = exp_lens2_parms
  \<rparr>"

locale Prod_Merge_Explicit_Spec

sublocale Prod_Merge_Explicit_Spec \<subseteq> Prod_Merge_Spec "prod_merge_explicit_parms"
  apply(unfold_locales)
          apply(auto)
  done

interpretation Prod_Merge_Explicit_Itp : Prod_Merge_Explicit_Spec
  done

end