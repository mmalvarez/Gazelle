theory View imports Main

begin

record ('d, 'r) view_parms =
  inj :: "('d * 'r) \<Rightarrow> 'r"
  prj :: "'r \<Rightarrow> 'd + 'r"

declare view_parms.defs[simp]

locale View =
  fixes View_parms :: "('d, 'r) view_parms"

begin
abbreviation inj :: "('d * 'r) \<Rightarrow> 'r" where
"inj \<equiv> view_parms.inj View_parms"

abbreviation prj :: "'r \<Rightarrow> 'd + 'r" where
"prj \<equiv> view_parms.prj View_parms"

end
print_context
locale View_Spec = View +
  assumes PrjInj1 :
    "\<And> (r :: 'b) (d :: 'a) . prj r = Inl d \<Longrightarrow> inj (d, r) = r"

(* i am unsure if we want this one.
   it may not be strong enough! *)
assumes PrjInj2 :
    "\<And> (r :: 'b) (r' :: 'b) . prj r = Inr r' \<Longrightarrow> r = r'"


assumes InjPrj1 :
    "\<And> (d :: 'a) (r :: 'b) (d' :: 'a) . prj (inj (d, r)) = Inl d' \<Longrightarrow> d = d'"

(* 
idea: if we fail to project after injecting, this must be because our original
structure was ill-formed. in that case there is nothing we can do to
correct the problem, so we should always return the same failure.
 *)
(* does this imply that prj r = Inr r? i think so *)
assumes InjPrj2 :
    "\<And> (d :: 'a) (r :: 'b) (r' :: 'b) (d' :: 'a) . prj (inj (d, r)) = Inr r' \<Longrightarrow> 
                 prj (inj (d', r)) = Inr r"


(*
assumes InjPrj :
    "\<And> (d :: 'a) (r :: 'b) . prj (inj (d, r)) = Inl d"
*)
assumes InjInj :
    "\<And> (a :: 'a) (b :: 'a) (c :: 'b) . inj (a, inj (b, c)) = inj (a, c)"


begin

lemma InjPrj2' :
    "\<And> (d :: 'a) (r :: 'b) (r' :: 'b) . prj (inj (d, r)) = Inr r' \<Longrightarrow> 
                r = r'"
  apply(frule_tac d' = d in  InjPrj2) apply(clarsimp)
  done

lemma InjPrj2'' :
  "
(\<forall> rx r'x dx . prj rx = Inr r'x \<longrightarrow> inj (dx, rx) = rx) \<Longrightarrow>
(\<forall> (d :: 'a) (r :: 'b) (r' :: 'b) (d' :: 'a) .
 prj (inj (d, r)) = Inr r' \<longrightarrow>
                 prj (inj (d', r)) = Inr r)"
  apply(clarsimp)
  apply(frule_tac PrjInj2) apply(clarsimp)
  apply(case_tac "local.prj r") apply(rotate_tac -1)
   apply(frule_tac PrjInj1) 
   apply(drule_tac x = "inj (d, r)" in spec) apply(clarsimp)
   apply(simp add:InjInj) apply(drule_tac x = a in spec) apply(clarsimp)

  apply(drule_tac x = r in spec) apply(clarsimp)
  done
(*
lemma NoRecovery :
  "\<And> b b' a .
      prj b = Inr b' \<Longrightarrow> prj(inj(a, b)) = Inr b"
  apply(case_tac "local.prj (local.inj (a, b))")
*)
(*
lemma InjPrj2''X :
  "\<And> r r' d . prj r = Inr r' \<Longrightarrow> inj (d, r) = r"
  apply(frule_tac PrjInj2) apply(clarsimp)
  apply(case_tac "prj (inj (d, r'))") 
  apply(frule_tac PrjInj1) apply(simp add:InjInj) 
  apply(frule_tac InjPrj1) apply(clarify)
  apply(rule_tac PrjInj1) apply(simp)*)
end


end