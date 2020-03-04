theory LatticeLike imports Main

begin

definition ord_leq :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where
"ord_leq o1 o2 = (\<forall> x1 x2 . o1 x1 x2 \<longrightarrow> o2 x1 x2)"

lemma ord_leq_refl : "\<And> ord . ord_leq ord ord"
  apply(simp add:ord_leq_def)
  done

lemma ord_leq_trans: "\<And> ox oy oz . ord_leq ox oy \<Longrightarrow> ord_leq oy oz \<Longrightarrow> ord_leq ox oz"
  apply(simp add:ord_leq_def)
  done

lemma ord_leq_antisym : "\<And> ox oy . ord_leq ox oy
 \<Longrightarrow> ord_leq oy ox \<Longrightarrow> ox = oy"
  apply(simp add:ord_leq_def)
  apply(blast)
  done

lemma ord_leq' : "\<And> ox oy a b .
  ord_leq ox oy \<Longrightarrow>
  ox a b \<Longrightarrow>
  oy a b"
  apply(simp add:ord_leq_def)
  done

(*
record ('a) latl_parms =
  lleq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  (*inf :: "'a \<Rightarrow> 'a \<Rightarrow> 'a option"*)
  bsup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

declare latl_parms.defs[simp]
*)
locale LatticeLike =
  fixes lleq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

begin

definition is_lb :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" where
"is_lb A a =
  (\<forall> x \<in> A . lleq a x)"

definition is_greatest :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
"is_greatest P a =
  (P a \<and>
   (\<forall> a' . P a' \<longrightarrow> lleq a' a))"

definition is_inf :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" where
"is_inf A a = is_greatest (is_lb A) a"

definition is_ub :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" where
"is_ub A a =
  (\<forall> x \<in> A . lleq x a)"

definition is_least :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
"is_least P a =
  (P a \<and>
   (\<forall> a' . P a' \<longrightarrow> lleq a a'))"

definition is_sup :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" where
"is_sup A a =
  is_least (is_ub A) a"

definition has_sup :: "'a set \<Rightarrow> bool" where
"has_sup A = (\<exists> s . is_sup A s)"

definition has_ub :: "'a set \<Rightarrow> bool" where
"has_ub A = (\<exists> s . is_ub A s)"

end

(*
(* double check this *)
(*
definition is_bub :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bub a a' s =
  (lleq a s \<and>
   (\<exists> y . is_sup {y' . lleq y' a' \<and> has_sup {y', a} } y \<and>
    lleq y s))"
*)

definition is_bub :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bub a a' s =
  (lleq a s \<and>
    (\<forall> y z . lleq y a' \<longrightarrow> is_sup {y, a} z \<longrightarrow> lleq z s))"

(* should this be is_greatest? *)
definition is_bsup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bsup a a' x = is_least (is_bub a a') x"

(* question: do we need a non-biased lower bound that is optional? *)

end
*)

(* idea: we want latticelike_weak to not have antisym*)


locale LatticeLike_Weak_Spec =
  LatticeLike +
  assumes
    leq_refl : "\<And> a . lleq a a"
  assumes
    leq_trans : "\<And> a b c . lleq a b \<Longrightarrow> lleq b c \<Longrightarrow> lleq a c"


locale LatticeLike_Spec =
    LatticeLike_Weak_Spec +
    assumes
    leq_antisym : "\<And> a b . lleq a b \<Longrightarrow> lleq b a \<Longrightarrow> a = b"

begin

lemma is_greatest_unique :
  "\<And> P a b . is_greatest P a \<Longrightarrow> is_greatest P b \<Longrightarrow> a = b"
  apply(auto simp add:is_greatest_def)
  apply(drule_tac x = b in spec) apply(drule_tac x = a in spec)
  apply(auto simp add:leq_antisym)
  done

lemma is_least_unique :
  "\<And> P a b . is_least P a \<Longrightarrow> is_least P b \<Longrightarrow> a = b"
  apply(auto simp add:is_least_def)
  apply(drule_tac x = b in spec) apply(drule_tac x = a in spec)
  apply(auto simp add:leq_antisym)
  done

end

locale Mergeable' =
  LatticeLike 

begin

(* i'm not sure if this is exactly what i had... *)
(*
definition is_bub :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bub a b s =
  (lleq a s \<and>
    ((\<forall> lleq' s' . ord_leq lleq lleq' \<longrightarrow>
                LatticeLike_Weak_Spec lleq' \<longrightarrow>
                LatticeLike.is_ub lleq' {a, b} s' \<longrightarrow>
                lleq' s' s)))"
*)
definition is_bub :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bub a b s =
  (lleq a s \<and>
    ((\<forall> lleq' s' . ord_leq lleq lleq' \<longrightarrow>
                LatticeLike_Weak_Spec lleq' \<longrightarrow>
                LatticeLike.is_sup lleq' {a, b} s' \<longrightarrow>
                lleq' s' s)))"

(* lleq' b s or lleq' s b ?
   is_sup or is_ub? *)

(* should this be is_greatest? *)
definition is_bsup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bsup a b x = is_least (is_bub a b) x"


end

locale Mergeable =
  Mergeable' +
  fixes bsup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

locale Mergeable_Spec =
  Mergeable +
  LatticeLike_Spec +
  assumes bsup_is_bsup:
    "\<And> a b . is_bsup a b (bsup a b)"

begin


lemma bsup_sup :
  "\<And> a b . has_sup {a, b} \<Longrightarrow> is_sup {a, b} (bsup a b)"
    apply(cut_tac a = a and b = b in bsup_is_bsup)
  apply(simp add:has_sup_def is_sup_def is_bsup_def is_bub_def is_ub_def is_least_def
        LatticeLike.is_sup_def LatticeLike.is_least_def) apply(auto)
  apply(drule_tac x = lleq in spec) apply(auto)
     apply(simp add:ord_leq_refl)
  apply(simp add: LatticeLike_Weak_Spec_axioms)
  apply(rotate_tac -1)
   apply(drule_tac x = s in spec) apply(auto)
     apply(simp add:is_ub_def)
  apply(simp add:is_ub_def)
   apply(rule_tac leq_trans) apply(simp) apply(simp)

  

  apply(rotate_tac -5)
  apply(drule_tac x = s in spec) apply(clarsimp)
  apply(drule_tac x = a' in spec) apply(clarsimp)
  apply(rotate_tac 3)
  apply(rule_tac b = s  in leq_trans)
   apply(clarsimp)
   apply(rotate_tac -1)
   apply(drule_tac x=  s in spec)
   apply(simp add:LatticeLike.is_ub_def) apply(auto)
   apply(rule_tac ox = lleq in ord_leq') apply(simp) apply(simp)
  apply(rule_tac ox = lleq in ord_leq') apply(simp) apply(simp)
  done
(*
lemma inf_assoc :
  "\<And> a b c . inf (inf a b) c = inf a (inf b c)"
  apply(cut_tac a = "local.inf a b" and b = c in inf_is_inf)
  apply(cut_tac a = a and b = b in inf_is_inf)
  apply(cut_tac a = a and b = "local.inf b c" in inf_is_inf)
  apply(cut_tac a = b and b = c in inf_is_inf)
  apply(auto simp add: is_inf_def)
(* i think we need a lemma here *)
  sorry
*)
end


abbreviation test0_parms :: "(nat option) latl_parms" where
"test0_parms \<equiv>
\<lparr> lleq = (\<lambda> l r .
    (case (l, r) of
      ((None), _) \<Rightarrow> True
       | _ \<Rightarrow> l = r))
, bsup = (\<lambda> l r .
    (case l of
            (None) \<Rightarrow> (r)
            | _ \<Rightarrow> l))
\<rparr>"

value "bsup test0_parms None (Some 2)"
value "bsup test0_parms (Some 2) (None)"


interpretation Test0 : LatticeLike_Spec test0_parms
  apply(unfold_locales)
  apply(auto)
       apply(simp split:option.splits)
       apply(simp split:option.splits)
      apply(simp split:option.splits)
     apply(simp add:LatticeLike.is_bsup_def LatticeLike.is_bub_def LatticeLike.is_least_def
                    LatticeLike.is_ub_def)
  apply(safe)
    apply(simp split:option.splits)
   apply(simp split:option.splits)
     apply(simp add:LatticeLike.is_sup_def LatticeLike.is_bsup_def LatticeLike.is_bub_def LatticeLike.is_least_def
                    LatticeLike.is_ub_def)
    apply(clarsimp)
    apply(case_tac a) apply(clarsimp) apply(simp)
     apply(simp add:LatticeLike.is_sup_def LatticeLike.is_bsup_def LatticeLike.is_bub_def LatticeLike.is_least_def
                    LatticeLike.is_ub_def)
   apply(clarsimp)

  apply(simp split:option.splits)
  apply(drule_tac x = b in spec) apply(clarsimp)
     apply(simp add:LatticeLike.is_sup_def LatticeLike.is_bsup_def LatticeLike.is_bub_def LatticeLike.is_least_def
                    LatticeLike.is_ub_def)
  done

abbreviation test_parms :: "(nat option * nat) latl_parms" where
"test_parms \<equiv>
\<lparr> lleq = (\<lambda> l r .
    (case (l, r) of
         ((None, l2), (None, r2)) \<Rightarrow> l2 = r2
       | ((None, l2), (Some r1, r2)) \<Rightarrow> l2 = r2
       | ((Some _, _), (None, _)) \<Rightarrow> False
       | ((Some l1, l2 ), (Some r1, r2)) \<Rightarrow> l1 = r1 \<and> l2 = r2))
, bsup = (\<lambda> l r .
    (case (l, r) of
            ((None, l2), (None, r2)) \<Rightarrow> (None, l2)
            |((None, l2), (Some r1, r2)) \<Rightarrow> (Some r1, l2)
            |((Some l1, l2), (None, r2)) \<Rightarrow> (Some l1, l2)
            |((Some l1, l2), (Some r1, r2)) \<Rightarrow> (Some l1, l2)))
\<rparr>"

value "bsup test_parms (None, 1) (Some 3, 2)"

interpretation Test : LatticeLike_Spec test_parms

  apply(unfold_locales)
     apply(simp split:prod.splits option.splits)
    apply(simp split:prod.splits option.splits)
    
   apply(simp) apply(simp split:prod.splits)
   apply(case_tac x1) apply(clarsimp)
    apply(case_tac x1a) apply(clarsimp) apply(clarsimp)
   apply(case_tac x1a) apply(clarsimp) apply(clarsimp)

  (* bsup *)
  apply(simp add: LatticeLike.is_bsup_def)
  apply(simp add: LatticeLike.is_least_def)
     apply(simp add:LatticeLike.is_sup_def LatticeLike.is_bsup_def LatticeLike.is_bub_def LatticeLike.is_least_def
                    LatticeLike.is_ub_def)
  apply(auto)
  apply(case_tac a) apply(clarsimp)
     apply(case_tac aa) apply(clarsimp) apply(clarsimp)
    apply(clarsimp)
    apply(case_tac aa) apply(clarsimp) apply(clarsimp)
   apply(simp split:option.split_asm)
    apply(auto)
  
  apply(case_tac a) apply(clarsimp)
(* a = None *)
  apply(auto)

   apply(case_tac aa) apply(clarsimp) apply(clarsimp)
(* aa = Some *)
  

   apply(case_tac ab) apply(clarsimp)
  apply(auto)
    apply(drule_tac x = "Some a" in spec) apply(clarsimp)
apply(drule_tac x = "Some a" in spec) apply(clarsimp)
apply(drule_tac x = "ba" in spec) apply(clarsimp)
    apply(drule_tac x = None in spec) apply(clarsimp)
  apply(auto)
     apply(clarsimp)
      apply(drule_tac x = None in spec) apply(clarsimp)


    apply(case_tac a) apply(clarsimp) apply(clarsimp)
      apply(case_tac aa) apply(clarsimp) apply(clarsimp)
     apply(case_tac a) 
apply(case_tac aa) apply(clarsimp) apply(clarsimp)
    apply(auto) apply(split option.split_asm)
    apply(auto)
    apply(drule_tac x = "Some ac" in spec)
      apply(drule_tac x = ba in spec) apply(auto)
      apply(drule_tac x = "Some ac" in spec) 
  apply(drule_tac x = b in spec)
  apply(clarsimp) apply(auto)
       apply(drule_tac x = ba in spec) apply(auto)
  
  apply(drule_tac x = "Some _" in spec)
    apply(auto)
    apply(simp split:option.splits)
  apply(auto)
  apply(rename_tac boo foo)
  apply(drule_tac x = baa in spec)
    apply(drule_tac x = None in spec) apply(clarsimp)
apply(drule_tac x = None in spec) apply(clarsimp)
     apply(clarsimp)
      apply(drule_tac x = None in spec) apply(clarsimp)
    apply(simp split: option.splits)

  apply(case_tac aa) apply(clarsimp) apply(clarsimp)
  apply(drule_tac x = None in spec) apply(clarsimp)
(*  apply(case_tac a) apply(clarsimp)
   apply(auto)
  apply(drule_tac x = None in spec) apply(clarsimp) *)
  apply(drule_tac x = "Some ab" in spec) 
  apply(drule_tac x = ba in spec)
  apply(simp)


   apply(simp)
   apply(simp add:LatticeLike.is_bsup_def LatticeLike.is_bub_def)
   apply(simp add:LatticeLike.is_least_def LatticeLike.is_bub_def)
   apply(simp add:LatticeLike.is_sup_def)
   apply(simp add:LatticeLike.is_least_def LatticeLike.is_ub_def)

   apply(clarsimp)
   apply(safe)
    apply(case_tac a) apply(clarsimp) apply(clarsimp)
   apply(case_tac a) apply(clarsimp) apply(drule_tac x = "None" in spec) apply(simp)

    apply(simp add:LatticeLike.has_ub_def LatticeLike.is_ub_def)
apply(simp add:LatticeLike.has_ub_def LatticeLike.is_ub_def)



  apply(unfold_locales)
  apply(auto)
       apply(simp split:option.splits)
       apply(simp split:option.splits)
      apply(simp split:option.splits)
     apply(simp split:option.splits)
    apply(simp split:option.splits if_split_asm)
     apply(simp add:LatticeLike.is_inf_def
                    LatticeLike.is_greatest_def
                    LatticeLike.is_lb_def)
     apply(simp add:LatticeLike.is_inf_def
                    LatticeLike.is_greatest_def
                    LatticeLike.is_lb_def)
  apply(clarsimp)
   apply(simp split:option.splits if_split_asm)

     apply(simp add:LatticeLike.is_bsup_def
                    LatticeLike.is_greatest_def
                    LatticeLike.is_least_def
                    LatticeLike.is_lb_def
                    LatticeLike.is_ub_def
                    LatticeLike.is_bub_def)
  apply(simp split:option.splits)
  apply(safe)
  apply(simp add:LatticeLike.has_sup_def LatticeLike.has_ub_def LatticeLike.is_sup_def LatticeLike.is_least_def LatticeLike.is_ub_def)
  apply(simp add:LatticeLike.has_sup_def LatticeLike.has_ub_def LatticeLike.is_sup_def LatticeLike.is_least_def LatticeLike.is_ub_def)
       apply(simp add:LatticeLike.has_sup_def LatticeLike.has_ub_def LatticeLike.is_sup_def LatticeLike.is_least_def LatticeLike.is_ub_def) 
      apply(simp add:LatticeLike.has_ub_def)
      apply(simp only:LatticeLike.is_ub_def latl_parms.simps)
      apply(drule_tac x = "Some x2" in spec) apply(clarify)
      apply(drule_tac x = ba in spec) apply(clarify)
  apply(simp)
      apply(simp add:LatticeLike.has_sup_def LatticeLike.has_ub_def LatticeLike.is_sup_def LatticeLike.is_least_def LatticeLike.is_ub_def)         apply(simp add:LatticeLike.has_sup_def LatticeLike.has_ub_def LatticeLike.is_sup_def LatticeLike.is_least_def LatticeLike.is_ub_def)         apply(simp add:LatticeLike.has_sup_def LatticeLike.has_ub_def LatticeLike.is_sup_def LatticeLike.is_least_def LatticeLike.is_ub_def)         apply(simp add:LatticeLike.has_sup_def LatticeLike.has_ub_def LatticeLike.is_sup_def LatticeLike.is_least_def LatticeLike.is_ub_def)         apply(simp add:LatticeLike.has_sup_def LatticeLike.has_ub_def LatticeLike.is_sup_def LatticeLike.is_least_def LatticeLike.is_ub_def)         
  apply(simp add:LatticeLike.has_sup_def LatticeLike.has_ub_def LatticeLike.is_sup_def LatticeLike.is_least_def LatticeLike.is_ub_def)
  apply(simp add:LatticeLike.has_sup_def LatticeLike.is_sup_def LatticeLike.is_least_def LatticeLike.is_ub_def)
       apply(simp add:LatticeLike.has_sup_def LatticeLike.is_sup_def LatticeLike.is_least_def LatticeLike.is_ub_def)
  apply(clarsimp)
      apply(simp add:LatticeLike.has_sup_def)
  apply(simp add:LatticeLike.is_sup_def)
  apply(simp add:LatticeLike.is_least_def)
  apply(simp only:LatticeLike.is_ub_def latl_parms.simps)

  apply(simp add:LatticeLike.has_sup_def LatticeLike.is_sup_def LatticeLike.is_least_def LatticeLike.is_ub_def)
  apply(simp add:LatticeLike.has_sup_def LatticeLike.is_sup_def LatticeLike.is_least_def LatticeLike.is_ub_def)
  apply(simp add:LatticeLike.has_sup_def LatticeLike.is_sup_def LatticeLike.is_least_def LatticeLike.is_ub_def)
  apply(simp add:LatticeLike.has_sup_def LatticeLike.is_sup_def LatticeLike.is_least_def LatticeLike.is_ub_def)
(* first idea: use option to create a pointed datatype.
   show it obeys the laws. *)
end