theory ViewRef4 imports "HOL-Lattice.Orders"
begin

record ('d, 'r) view_ref_parms =
  inj :: "'d \<Rightarrow> 'r \<Rightarrow> 'r"
  prj :: "'r \<Rightarrow> 'd"
  refnd :: "'d \<Rightarrow> 'd \<Rightarrow> bool"
  refnr :: "'r \<Rightarrow> 'r \<Rightarrow> bool"

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

abbreviation refnd :: "'d \<Rightarrow> 'd \<Rightarrow> bool" where
"refnd \<equiv> view_ref_parms.refnd View_Ref_parms"

abbreviation refnr :: "'r \<Rightarrow> 'r \<Rightarrow> bool" where
"refnr \<equiv> view_ref_parms.refnr View_Ref_parms"
end

locale View_Ref_Spec = View_Ref +
  DO : partial_order "refnd"  +
  RO : partial_order "refnr" +


(* add an assumption about refining r to r'? *)
assumes RefnInjD :
    "\<And> (d :: 'a) (d' :: 'a) (r :: 'b) . refnd d d' \<Longrightarrow>
        refnr (inj d r) (inj d' r)"

(* i am skeptical about this rule. *)

assumes RefnInjR :
    "\<And> (r :: 'b) (r' :: 'b) (d :: 'a) . refnr r r' \<Longrightarrow>
        refnr (inj d r) (inj d r')"

  assumes RefnPrj :
    "\<And> (r :: 'b) (r' :: 'b) (d :: 'a) . refnr r r' \<Longrightarrow>
      refnd (prj r) (prj r')"          

  assumes PrjInj :
    "\<And> (r :: 'b) . inj (prj r) r = r"

  assumes InjPrj :
    "\<And> (d :: 'a) (r :: 'b) (d' :: 'a) . refnd d (prj (inj d r))"

  assumes InjInj :
    "\<And> (a :: 'a) (b :: 'a) (c :: 'b) . refnr (inj a c) (inj a (inj b c))"

begin

lemma RefnInj' :
      "\<And> (d :: 'a) (d' :: 'a) (r :: 'b) (r' :: 'b) . refnd d d' \<Longrightarrow>
        refnr r r' \<Longrightarrow>
        refnr (inj d r) (inj d' r')"
  apply(frule_tac r = r in RefnInjD)
  apply(frule_tac d = d' in RefnInjR)
  apply(drule_tac x = "local.inj d r" and z = "inj d' r'" in RO.leq_trans) 
   apply(auto)
  done
(*
lemma RefnPrj2 :
    "\<And> (r :: 'b) (r' :: 'b) (d :: 'a) (d' :: 'a) . refnr r r' \<Longrightarrow>
        prj r = Inl d \<Longrightarrow>
        prj r' = Inl d' \<Longrightarrow>
        (refnd d d')"  
  apply(cut_tac r = r and r' = r' and d = d in "RefnPrj") apply(auto)
  done
*)
end

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