theory ViewRef3 imports "HOL-Lattice.Orders"
begin
record ('d, 'r) view_ref_parms =
  inj :: "'d \<Rightarrow> 'r \<Rightarrow> 'r"
  prj :: "'r \<Rightarrow> 'd"
  refn :: "'d \<Rightarrow> 'd \<Rightarrow> bool"

(*
record ('d1, 'd2, 'r) view_ref_merge_parms =
  v1 :: "('d1, 'r) view_parms"
  v2 :: "('d2, 'r) view_parms"
*)
declare view_ref_parms.defs[simp]

locale View_Ref =
  fixes View_Ref_parms :: "('d, 'r) view_ref_parms"
begin

abbreviation inj :: "'d \<Rightarrow> 'r \<Rightarrow> 'r" where
"inj \<equiv> view_ref_parms.inj View_Ref_parms"

abbreviation prj :: "'r \<Rightarrow> 'd" where
"prj \<equiv> view_ref_parms.prj View_Ref_parms"

abbreviation refn :: "'d \<Rightarrow> 'd \<Rightarrow> bool" where
"refn \<equiv> view_ref_parms.refn View_Ref_parms"


end

locale View_Ref_Spec = View_Ref +
  DO : partial_order "refn" + 

(*
assumes RefnInj :
    "\<And> (d :: 'a) (d' :: 'a) (r :: 'b) . refnd d d' \<Longrightarrow>
        refnr (inj (d, r)) (inj (d', r))"
*)
(*
  assumes RefnPrj :
    "\<And> (r :: 'b) (r' :: 'b) (d :: 'a) . refnr r r' \<Longrightarrow>
        prj r = Inl d \<Longrightarrow>
        (\<exists> d' . prj r' = Inl d' \<and> refnd d d')"     
*)
  assumes PrjInj :
    "\<And> (d :: 'a) (r :: 'b) . refn d (prj r) \<Longrightarrow> inj d r = r"

  assumes InjPrj :
    "\<And> (d :: 'a) (d' :: 'a) (r :: 'b)  . refn d d' \<Longrightarrow> refn d (prj (inj d' r))"

  assumes InjInj :
    "\<And> (a :: 'a) (b :: 'a) (c :: 'b) . 
      \<exists> ab . refn a ab \<and> prj (inj ab c) = ab \<and> inj a (inj b c) = inj ab c"

begin

lemma InjPrj' :
 "\<And> (d :: 'a) (r :: 'b)  . refn d (prj (inj d r))"
  apply(rule_tac InjPrj)
  apply(simp add: DO.leq_refl)
  done

lemma PrjInj' :
  "\<And> (r :: 'b) . inj (prj r) r = r"

  apply(rule_tac PrjInj) apply(simp add: DO.leq_refl)
  done

end
(*
begin
lemma RefnPrj2 :
    "\<And> (r :: 'b) (r' :: 'b) (d :: 'a) (d' :: 'a) . refnr r r' \<Longrightarrow>
        prj r = Inl d \<Longrightarrow>
        prj r' = Inl d' \<Longrightarrow>
        (refnd d d')"  
  apply(cut_tac r = r and r' = r' and d = d in "RefnPrj") apply(auto)
  done

end
*)
(* next: View_Ref_Merge
    idea: 

coherence (original)
      V1.prj r = Inl d1 \<Longrightarrow> V2.prj r = Inl d2 \<Longrightarrow>
      V1.inj (d1, V2.inj (d2, r')) = V2.inj (d2, V1.inj (d1, r'))"

coherence (new)
      V1.prj r = Inl d1 \<Longrightarrow> V2.prj r = Inl d2 \<Longrightarrow>
      V1.inj (d1, V2.inj (d2, r')) = V2.inj (d2, V1.inj (d1, r'))"
    
can we get away with the same definition?

*)

end