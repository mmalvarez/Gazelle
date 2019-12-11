theory View_Comp imports View
begin

(* "vertical" composition of views
(analogous to function composition)
*)
record ('d, 'r1, 'r2) view_comp_parms =
  v1 :: "('d, 'r1) view_parms"
  v2 :: "('r1, 'r2) view_parms"

declare view_comp_parms.defs[simp]

locale View_Comp'  =
  fixes View_Comp_parms :: "('d, 'r1, 'r2) view_comp_parms"

locale View_Comp_Spec = View_Comp' +
  V1 : View_Spec "v1 View_Comp_parms" +
  V2 : View_Spec "v2 View_Comp_parms"

begin

print_context

(* there is a problem here
   i think the problem is that V1.inj (d, r1)
   may do something very weird if V1.prj r1 isnt
   Inl (?)
 *)

(*
fun inj' :: "('a * 'c) \<Rightarrow> 'c" where
  "inj' (d, r2) =
    (case V2.prj r2 of
      Inl r1 \<Rightarrow> V2.inj (V1.inj (d, r1), r2)
      | Inr r2 \<Rightarrow> r2)"
*)

(* I am worried this is too weak. It means we can only inject elements
   that represent a projectable r1. However the stronger formulations (below)
   seem to all fail. *)
fun inj' :: "('a * 'c) \<Rightarrow> 'c" where
  "inj' (d, r2) =
    (case V2.prj r2 of
      Inl r1 \<Rightarrow> (case V1.prj r1 of
          Inl _ \<Rightarrow> V2.inj (V1.inj (d, r1), r2)
          | Inr _ \<Rightarrow> r2)
      | Inr r2 \<Rightarrow> r2)"

(*
fun inj' :: "('a * 'c) \<Rightarrow> 'c" where
  "inj' (d, r2) =
    (case V2.prj r2 of
      Inl r1 \<Rightarrow> (case V1.prj (V1.inj (d, r1)) of
          Inl _ \<Rightarrow> V2.inj (V1.inj (d, r1), r2)
          | Inr _ \<Rightarrow> r2)
      | Inr r2 \<Rightarrow> r2)"
*)
(*
fun inj' :: "('a * 'c) \<Rightarrow> 'c" where
  "inj' (d, r2) =
    (case V2.prj r2 of
      Inl r1 \<Rightarrow> (case V2.prj (V2.inj (V1.inj (d, r1), r2)) of
                    Inl _ \<Rightarrow> V2.inj (V1.inj (d, r1), r2)
                    | Inr _ => r2)
      | Inr r2 \<Rightarrow> r2)"
*)
(*
fun prj' :: "'c \<Rightarrow> ('a + 'c)" where
  "prj' r2 =
    (case V2.prj r2 of
      Inl r1 \<Rightarrow> (case V1.prj r1 of
        Inl d \<Rightarrow> Inl d
        | Inr r1 \<Rightarrow> Inr (V2.inj (r1, r2)))
      | Inr r2 \<Rightarrow> Inr r2)"    
*)

fun prj' :: "'c \<Rightarrow> ('a + 'c)" where
  "prj' r2 =
    (case V2.prj r2 of
      Inl r1 \<Rightarrow> (case V1.prj r1 of
        Inl d \<Rightarrow> Inl d
        | Inr r1 \<Rightarrow> Inr r2)
      | Inr r2 \<Rightarrow> Inr r2)"    

abbreviation vp :: "('a, 'c) view_parms" where
"vp \<equiv> \<lparr> inj = inj', prj = prj' \<rparr>"

end


(* TODO make this proof less awful *)
(* vertical composition of views*)
sublocale View_Comp_Spec \<subseteq> View_Spec "vp"
  apply(unfold_locales)
      apply(simp add: V1.PrjInj1 V2.PrjInj1 split: sum.splits prod.splits)

     apply(simp)
(* this is laughably inefficient *)
    apply(simp add: V1.InjPrj1 V2.InjPrj1  V1.InjPrj2 V2.InjPrj2 V1.PrjInj1 V2.PrjInj1 V1.PrjInj2 V2.PrjInj2  split: sum.splits prod.splits)

    apply(simp add: V1.InjPrj1 V2.InjPrj1  V1.InjPrj2 V2.InjPrj2 V1.PrjInj1 V2.PrjInj1 V1.PrjInj2 V2.PrjInj2  split: sum.splits prod.splits)
     apply(clarsimp)
     apply(frule_tac V2.InjPrj1) apply(clarsimp)
     apply(frule_tac V1.InjPrj1) apply(clarsimp)

  apply(clarsimp)
    apply(frule_tac V2.PrjInj2) apply(clarsimp)

  apply(simp)

  apply(simp split: sum.splits prod.splits)
      apply(safe)
           apply(frule_tac V1.PrjInj2) apply(clarsimp)
             apply(frule_tac V2.InjPrj1)
           apply(rotate_tac -2)
           apply(frule_tac V2.InjPrj1)
           apply(clarsimp)
           apply(frule_tac d' = d in V1.InjPrj2) apply(clarsimp)

          apply(frule_tac V1.PrjInj2) apply(clarsimp)
          apply(frule_tac r = x1c in V1.PrjInj2) apply(clarsimp)
          apply(frule_tac V1.PrjInj2) apply(clarsimp)
          apply(frule_tac V1.PrjInj2) apply(clarsimp)
    apply(frule_tac V2.InjPrj1) apply(clarsimp)
          apply(frule_tac d' = x2a in V2.InjPrj1) apply(clarsimp)
          apply(frule_tac d = d and d' = d' in V1.InjPrj2) apply(clarsimp)

           apply(frule_tac V1.PrjInj2) apply(clarsimp)
             apply(frule_tac V2.InjPrj1)
           apply(rotate_tac -2)
           apply(frule_tac V2.InjPrj1)
           apply(clarsimp)
         apply(frule_tac d' = d in V1.InjPrj2) apply(clarsimp)

        apply(frule_tac V1.PrjInj2) apply(clarsimp)

           apply(frule_tac V2.PrjInj2) apply(clarsimp)

      apply(simp add: V2.InjPrj2)

     apply(simp add: V2.InjPrj2)

    apply(frule_tac r' = x2a and d' = "V1.inj (d', x1)" in V2.InjPrj2) apply(clarsimp)

   apply(drule_tac V2.PrjInj2)
   apply(drule_tac V2.PrjInj2) apply(simp)


  apply(clarsimp)
  apply(simp split: sum.splits prod.splits)
  apply(safe)

      apply(simp add: V2.InjInj)
      apply(frule_tac V2.InjPrj1) apply(clarsimp)
      apply(simp add: V1.InjInj)

     apply(frule_tac V1.PrjInj2) apply(clarsimp)
      apply(frule_tac V2.InjPrj1) apply(clarsimp)
     apply(frule_tac d' = "a" in V1.InjPrj2)
     apply(rotate_tac -1)
     apply(frule_tac V1.PrjInj2) apply(clarsimp)

    apply(frule_tac d' = "V1.inj (a, x1)" in V2.InjPrj2)
    apply(frule_tac V2.PrjInj2)  apply(clarsimp)
    apply(rotate_tac -2)
    apply(frule_tac V2.PrjInj2)  apply(clarsimp)

    apply(frule_tac V2.PrjInj2)  apply(clarsimp)
    apply(frule_tac V2.PrjInj2)  apply(clarsimp)
  done



end