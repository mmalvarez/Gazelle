theory View_Merge imports View

begin

(* "horizontal" composition of views *)

record ('d1, 'd2, 'r) view_merge_parms =
  v1 :: "('d1, 'r) view_parms"
  v2 :: "('d2, 'r) view_parms"

declare view_merge_parms.defs[simp]

(* i don't know that this is super useful. but maybe it is? *)
locale View_Merge'  =
  fixes View_Merge_parms:: "('d, 'r1, 'r2) view_merge_parms"

locale View_Merge_Spec = View_Merge' +
  V1 : View_Spec "v1 View_Merge_parms" +
  V2 : View_Spec "v2 View_Merge_parms" +
  assumes Coh :
    "\<And> r d1 d2 r' .
      V1.prj r = Inl d1 \<Longrightarrow> V2.prj r = Inl d2 \<Longrightarrow>
      V1.inj (d1, V2.inj (d2, r')) = V2.inj (d2, V1.inj (d1, r'))"


begin

end

locale View_Merge_Spec_Total = View_Merge_Spec +
  assumes Tot: "\<And> r . (\<exists> d1 . V1.prj r = Inl d1) \<or> (\<exists> d2 . V2.prj r = Inl d2)"

begin

end


record ('d, 'r1, 'r2) view_comerge_parms =
  v1 :: "('d, 'r1) view_parms"
  v2 :: "('d, 'r2) view_parms"

declare view_comerge_parms.defs[simp]

locale View_Comerge'  =
  fixes View_Comerge_parms :: "('a, 'b, 'c) view_comerge_parms"

locale View_Comerge_Spec = View_Comerge' +
  V1 : View_Spec "v1 View_Comerge_parms" +
  V2 : View_Spec "v2 View_Comerge_parms"

begin

end

(* let's see what specs we need to make the proof go through. *)
(* this doesn't seem like a useful construct. *)
locale View_Comerge_View = View_Comerge_Spec 
begin

fun inj' :: "('b * 'c) \<Rightarrow> 'c" where
"inj' (b, c) = 
  (case V1.prj b of
      Inl a \<Rightarrow> V2.inj (a, c)
    | Inr _ \<Rightarrow> c)"

fun prj' :: "'c \<Rightarrow> ('b + 'c)" where
"prj' c =
  (case V2.prj c of
      Inl a \<Rightarrow> Inl (V1.inj (a, undefined))
      | Inr _ \<Rightarrow> Inr c)"

abbreviation vp :: "('b, 'c) view_parms" where
"vp \<equiv> \<lparr> inj = inj', prj = prj' \<rparr>"

end

(* we don't actually need this for functions,
i think *)
(*
sublocale View_Comerge_View \<subseteq> View_Spec "vp"
  apply(unfold_locales)
      apply(clarsimp)
      apply(simp split:sum.splits)
      apply(clarsimp)
  apply(drule_tac V1.InjPrj1)
      apply(frule_tac V2.PrjInj1) apply(clarsimp)

  apply(clarsimp)
      apply(simp split:sum.splits)

  apply(clarsimp)
    apply(simp split:sum.splits)
     apply(frule_tac V2.InjPrj1) apply(clarsimp)
     apply(frule_tac V1.PrjInj1)
(* we need V1 to be prismlike. *)
     defer

(* we should be able to get a contradiction here. *)

     apply(frule_tac V1.PrjInj2) apply(clarsimp)
     apply(frule_tac V2.PrjInj1) 
     apply(case_tac "V1.prj x2") apply(clarsimp)
  apply(clarsimp)
     apply(case_tac "V1.prj (V1.inj (x1, x2))")
      defer (* v1 prismlike takes care of this case *)
      apply(frule_tac d' = x1 in V1.InjPrj2)
      
      apply(clarsimp)
  apply(frule_tac V1.InjPrj1) apply(clarsimp)
apply(frule_tac V2.PrjInj1)
       apply(frule_tac V1.InjPrj1) apply(clarsimp)
     apply(frule_tac V1.PrjInj1)

(* idea: just like for lenses/prisms we are going to have a concerete version *)
*)
end