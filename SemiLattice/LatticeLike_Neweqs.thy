theory LatticeLike_Neweqs imports Main HOL.Transitive_Closure

begin

definition ord_leq :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where
"ord_leq o1 o2 = (\<forall> x1 x2 . o1 x1 x2 \<longrightarrow> o2 x1 x2)"

definition ord_extends :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"ord_extends o1 o2 =
  (ord_leq o1 o2 \<and>
  (\<forall> x1 x2 . o2 x1 x2 \<longrightarrow>
       ((\<exists> p1 p2 . o1 x1 p1 \<and> o2 p1 p2 \<and> o2 p2 p1 \<and> o1 p2 x2))))"

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

lemma ord_leq_d : "\<And> ox oy a b .
  ox a b \<Longrightarrow>
  ord_leq ox oy \<Longrightarrow>
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


(*
definition is_bub :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bub a b s =
  (lleq a s \<and>
    ((\<forall> lleq'S eqs . lleq'S = add_eqs {(a, b) . lleq a b} eqs \<longrightarrow>
                (a, b) \<in> lleq'S \<longrightarrow>
                ((s, b) \<in> lleq'S \<and>
                 (b, s) \<in> lleq'S))))"
*)



definition is_bub :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bub a b s =
  (lleq a s \<and>
    ((\<forall> lleq' s' . ord_extends lleq lleq' \<longrightarrow>
                LatticeLike_Weak_Spec lleq' \<longrightarrow>
                LatticeLike.is_sup lleq' {a, b} s' \<longrightarrow>
                lleq a s' \<longrightarrow>
                lleq' s' s)))"

(*
LatticeLike.is_ub lleq' {a, b} s' \<longrightarrow>
                lleq' s' s'
*)

definition is_bub_weak :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bub_weak a b s =
  (lleq a s \<and>
    ((\<forall> lleq' . ord_leq lleq lleq' \<longrightarrow>
                lleq' a b \<longrightarrow>
                (lleq' b s))))"


(* should this be is_greatest? *)

definition is_bsup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bsup a b x = is_least (is_bub a b) x"

definition is_bsup_weak :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bsup_weak a b x = is_least (is_bub_weak a b) x"

inductive clos :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)" where
"\<And> R a . clos R a a"
| "\<And> R a b  . R a b \<Longrightarrow> clos R a b"
| "\<And> R a b c. clos R a b \<Longrightarrow> clos R b c \<Longrightarrow> clos R a c"
end


locale Mergeable =
  Mergeable' +
  fixes bsup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

locale Mergeable_Spec =
  Mergeable +
  LatticeLike_Spec +



  assumes bsup_is_bsup:
    "\<And> a b . is_bsup a b (bsup a b)"
(*

assumes bsup_is_bsup' :
      "\<And> a b . is_bsup' a b (bsup a b)"

assumes bsup_is_bsup3 :
      "\<And> a b . is_bsup3 a b (bsup a b)"
*)
(*
assumes bsup_is_bsup' :
    "\<And> a b . is_bsup' a b (bsup a b)"

assumes bsup_is_bsup'' :
    "\<And> a b . is_bsup'' a b (bsup a b)"

assumes bsup_is_bsup3 :
    "\<And> a b . is_bsup3 a b (bsup a b)"
*)
(*
assumes bsup_is_bsup4 :
  "\<And> a b . is_bsup4 a b (bsup a b)"
*)

(*
assumes bsup_is_bsup4' :
  "\<And> a b . is_bsup4' a b (bsup a b)"
*)

(*
assumes bsup_weak_is_bsup :
    "\<And> a b . is_bsup_weak a b (bsup_weak a b)"
*)
begin


lemma bsup_sup_weak :
  "\<And> a b x . has_sup {a, b} \<Longrightarrow> is_bsup_weak a b x \<Longrightarrow>
             is_sup {a, b} x"
  apply(simp add:has_sup_def is_sup_def is_bsup_def is_bub_def is_ub_def is_least_def
        LatticeLike.is_sup_def LatticeLike.is_least_def is_greatest_def
        is_bsup_weak_def is_bub_weak_def) apply(auto)
   apply(drule_tac x = s in spec) apply(auto)
    apply(simp add:ord_leq_def)

(*
   apply(drule_tac x = "\<lambda> a' b' . b' = b \<or> lleq a' b'" in spec) apply(auto)
    apply(simp add:ord_leq_def) apply(simp add:leq_refl)

  apply(drule_tac x = a' in spec) apply(auto)
   apply(simp add:ord_leq_def)
*)
   apply(drule_tac x = "\<lambda> a' b' . a' = a \<or> lleq a' b'" in spec) apply(auto)
    apply(simp add:ord_leq_def)

  apply(drule_tac x = a' in spec) apply(auto)
   apply(simp add:ord_leq_def)

  done

(*
(* closure operator? *)
  lemma bsup_sup4' :
  "\<And> a b . has_sup {a, b} \<Longrightarrow> is_sup {a, b} (bsup a b)"
    apply(cut_tac a = a and b = b in bsup_is_bsup4')
  apply(simp add: is_bsup'_def is_bub'_def has_sup_def is_sup_def is_bsup_def is_bub_def is_ub_def is_least_def
        LatticeLike.is_sup_def LatticeLike.is_least_def is_greatest_def is_bsup4_def is_bub4_def
        is_bsup4'_def is_bub4'_def) apply(auto)


   apply(drule_tac x = "(\<lambda> a' b' . lleq a' b' \<or> (lleq a' a))" in spec) apply(auto)
             defer defer
    apply(simp add: leq_refl)
            defer
            defer
    apply(drule_tac x = a in spec) apply(auto)
       apply(simp add: leq_refl)
         
            apply(drule_tac x = s in spec) apply(auto)
    defer
    apply(simp add: leq_refl)

   apply(drule_tac x = "(\<lambda> a' b' . lleq a' b' \<or> (lleq a' a))" in spec) apply(auto)
             defer defer
    apply(simp add: leq_refl)
*)

lemma bsup_sup :
  "\<And> a b . has_sup {a, b} \<Longrightarrow> is_sup {a, b} (bsup a b)"
    apply(cut_tac a = a and b = b in bsup_is_bsup)
  apply(simp add: is_bsup_def is_bub_def has_sup_def is_sup_def is_bsup_def is_bub_def is_ub_def is_least_def
        LatticeLike.is_sup_def LatticeLike.is_least_def is_greatest_def ) apply(auto)

   apply(drule_tac x = "lleq" in spec) 
   apply(auto)
     apply(simp add:ord_extends_def) apply(simp add:ord_leq_refl)
     apply(clarsimp)

  apply(drule_tac x = s in spec)
   apply(auto)
     apply(simp add: LatticeLike.is_ub_def is_ub_def) apply(clarsimp)
      apply(rotate_tac -5)
      apply(drule_tac x = s in spec) apply(auto)
  apply(drule_tac a = a and b = s in ord_leq') apply(simp) apply(simp)
      apply(drule_tac a = b and b = s in ord_leq') apply(simp) apply(simp)
  apply(rotate_tac -2)
  apply(drule_tac x = x2 in spec)  apply(auto)

    apply(simp add: LatticeLike.is_ub_def)

  apply(drule_tac a = b and b = s and c = "bsup a b" in leq_trans) apply(auto)

(* s or a'? *)
    apply(drule_tac x = a' in spec) apply(auto)

  apply(drule_tac x = "lleq'" in spec) apply(rotate_tac -1) apply(auto)
  apply(simp add:LatticeLike.is_ub_def)
  apply(rotate_tac -2)
  apply(drule_tac x = a' in spec) apply(auto)
  apply(simp add:ord_extends_def) apply(clarsimp)
   apply(drule_tac ox = lleq and a = a and b = a' in ord_leq') apply(auto)
  apply(simp add:ord_extends_def) apply(clarsimp)
  apply(drule_tac ox = lleq and a = b and b = a' in ord_leq') apply(auto)
  done

(*
lemma bsup_sup3' :
  "\<And> a b . has_sup {a, b} \<Longrightarrow> is_sup {a, b} (bsup a b)"
    apply(cut_tac a = a and b = b in bsup_is_bsup3)
  apply(simp add: is_bsup'_def is_bub'_def has_sup_def is_sup_def is_bsup_def is_bub_def is_ub_def is_least_def
        LatticeLike.is_sup_def LatticeLike.is_least_def is_greatest_def is_bsup4_def is_bub4_def is_bsup3'_def is_bub3_def is_bsup3_def) apply(auto)

   apply(drule_tac x = "(\<lambda> a' b' . lleq a' b' \<or> (lleq a' a) \<or> (lleq b b'))" in spec) apply(auto)
             defer
             defer
                      apply(simp add:leq_refl)
                      apply(simp add:leq_refl)
apply(simp add:leq_refl)
            apply(rule_tac b = a in leq_trans) apply(simp) apply(simp)
           apply(rule_tac b = a in leq_trans) apply(simp) apply(simp)
          apply(simp add:leq_refl)
         apply(rule_tac b = a in leq_trans) apply(simp) apply(simp)
           apply(rule_tac b = a in leq_trans) apply(simp) apply(simp)
          apply(simp add:leq_refl)
           apply(rule_tac b = a in leq_trans) apply(simp) apply(simp)
     apply(rule_tac b = a in leq_trans) apply(simp) apply(simp)

    apply(drule_tac x = "(\<lambda> a' b' . lleq a' b' \<or> (lleq a' a))" in spec) apply(clarsimp)
    apply(safe)
                      defer
                      defer
  apply(simp add:leq_refl)
                      apply(cut_tac a = b and b = "bsup a b" in leq_antisym)
  apply(simp) apply(simp) apply(simp)
                      apply(drule_tac x = a' in spec) apply(simp)
  apply(safe)
   apply(drule_tac x = s in spec) apply(auto)

   apply(drule_tac x = "(\<lambda> a' b' . lleq a' b' \<or> (lleq a' a))" in spec) apply(auto)
              defer
              defer
  apply(simp add:leq_refl)
*)
(*
lemma bsup_sup3 :
  "\<And> a b . has_sup {a, b} \<Longrightarrow> is_sup {a, b} (bsup a b)"
    apply(cut_tac a = a and b = b in bsup_is_bsup3)
  apply(simp add: is_bsup'_def is_bsup''_def is_bsup3_def is_bub3_def is_bub'_def has_sup_def is_sup_def is_bsup_def is_bub_def is_ub_def is_least_def
        LatticeLike.is_sup_def LatticeLike.is_least_def is_greatest_def) apply(auto)

   apply(drule_tac x = s in spec) apply(auto)
    apply(simp add:ord_leq_def)
*)
(*
lemma bsup_sup2 :
  "\<And> a b . has_sup {a, b} \<Longrightarrow> is_sup {a, b} (bsup a b)"
    apply(cut_tac a = a and b = b in bsup_is_bsup')
  apply(simp add: is_bsup'_def is_bub'_def has_sup_def is_sup_def is_bsup_def is_bub_def is_ub_def is_least_def
        LatticeLike.is_sup_def LatticeLike.is_least_def is_greatest_def) apply(auto)

   apply(drule_tac x = s in spec) apply(auto)
    apply(drule_tac x = "bsup a b" in spec) apply(auto)

  defer

  apply(rule_tac leq_trans) apply(simp) apply(simp)

   apply(drule_tac x = "(\<lambda> a' b' . lleq a' b' \<or> (lleq a' a))" in spec) apply(auto)
             apply(simp add:ord_leq_def)
            defer
         apply(simp add:leq_refl)

           apply(drule_tac x = "bsup a b" in spec) apply(auto)
  defer
            apply(drule_tac a = "bsup a b" and c = a' in leq_trans) apply(simp) apply(simp)
           apply(drule_tac a = "a" and b = "bsup a b" in leq_antisym) apply(simp)
           apply(simp)
            apply(drule_tac a = "bsup a b" and c = a' in leq_trans) apply(simp) apply(simp)
            apply(drule_tac a = "bsup a b" and c = a' in leq_trans) apply(simp) apply(simp)
            apply(drule_tac a = "bsup a b" and c = a' in leq_trans) apply(simp) apply(simp)
            apply(drule_tac a = "bsup a b" and c = a' in leq_trans) apply(simp) apply(simp)
            apply(drule_tac a = "bsup a b" and c = a' in leq_trans) apply(simp) apply(simp)
            apply(drule_tac a = "bsup a b" and c = a' in leq_trans) apply(simp) apply(simp)

   apply(drule_tac x = "(\<lambda> a' b' . lleq' a' b' \<or> (lleq s b))" in spec) apply(auto)
  defer defer
(*
   apply(drule_tac x = "(\<lambda> a' b' . lleq a' b' \<or> (lleq a' a))" in spec) apply(auto)
          apply(simp add:ord_leq_def)
  defer

         apply(simp add:leq_refl)
       apply(rule_tac leq_trans) apply(auto)
  apply(simp add:leq_refl)
       apply(rule_tac leq_trans) apply(auto)

   apply(drule_tac x = a' in spec) apply(auto)
   defer

   apply(simp add:LatticeLike_Weak_Spec_def)
   apply(auto)
        apply(simp add:leq_refl)
      apply(drule_tac a = aa and b = ba in leq_trans) apply(simp) apply(simp)
   apply(drule_tac a = aa and b = ba in leq_trans) apply(simp) apply(simp)

  apply(drule_tac a = b and b = a' in ord_leq')
   apply(simp) apply(simp) *)
  sorry
*)
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


fun test0_lleq :: "nat option \<Rightarrow> nat option \<Rightarrow> bool" where
"test0_lleq None _ = True"
| "test0_lleq x y = (x = y)"

fun test0_bsup :: "nat option \<Rightarrow> nat option \<Rightarrow> nat option" where
"test0_bsup None r = r"
| "test0_bsup l r = l"
  

value "test0_bsup None (Some 2)"
value "test0_bsup (Some 2) (None)"

(*
interpretation Test0 : Mergeable_Spec test0_lleq test0_bsup
  apply(unfold_locales)
     apply(case_tac a; clarsimp) 
    apply(case_tac a; clarsimp)
   apply(case_tac a; clarsimp)
   apply(case_tac b; clarsimp)

  apply(simp add:Mergeable'.is_bsup_weak_def Mergeable'.is_bsup_def Mergeable'.is_bub_def LatticeLike.is_least_def LatticeLike.is_sup_def LatticeLike.is_ub_def
                 Mergeable'.is_bub_weak_def)

  apply(auto)
   apply(case_tac a; clarsimp)
   apply(case_tac a; clarsimp) 
    apply(simp add: ord_extends_def)
    apply(clarsimp)
    apply(drule_tac x = b in spec) apply(auto)
  apply(drule_tac  a = None and b = b in ord_leq') 
      apply(case_tac b; clarsimp)
     apply(case_tac b; clarsimp)
  apply(drule_tac  a = b and b = b in ord_leq') 
     apply(case_tac b; clarsimp) apply(clarsimp)


(*
   apply(simp add:ord_extends_def)
   apply(auto)
   apply(rotate_tac -1)
   apply(drule_tac x = s' in spec)
*)
  apply(simp add:ord_extends_def; clarsimp)
   apply(case_tac s'; auto)
    apply(drule_tac a = "None" and b = "Some aa" in ord_leq') apply(auto)
  apply(rotate_tac -1)

  apply(case_tac b; auto)
  apply(rotate_tac -2)
   apply(drule_tac x = "Some aa" in spec)
    apply(rotate_tac -1) apply(auto)
      apply(drule_tac a = "Some aa" and b = "Some aa" in ord_leq') apply(auto)

    apply(drule_tac a = "None" and b = "Some aa" in ord_leq') apply(auto)

(* ab? *)
   apply(frule_tac x = "Some aa" in spec)
  apply(rotate_tac -1)
apply(drule_tac x = "Some a" in spec)
   apply(auto)

  apply(drule_tac x = test0_lleq in spec)
  apply(auto)
    apply(simp add:ord_extends_def)
    apply(simp add:ord_leq_refl)

(* shouldn't need to reprove *)
  apply(simp add:LatticeLike_Weak_Spec_def)
     apply(case_tac a; clarsimp) 
   apply(case_tac b; clarsimp)
   apply(case_tac a'; clarsimp)
    apply(auto)
      apply(case_tac a; clarsimp)
     apply(case_tac a; clarsimp)
  apply(case_tac ab; clarsimp)

   apply(case_tac ab; clarsimp)




  apply(case_tac a; auto)
   apply(case_tac b; auto)

  done
*)

definition test_lleq :: "(nat option * nat) \<Rightarrow> (nat option * nat) \<Rightarrow> bool" where
(*
"test_lleq l r =
(case (l, r) of
         ((None, l2), (None, r2)) \<Rightarrow> l2 = r2
       | ((None, l2), (Some r1, r2)) \<Rightarrow> l2 = r2
       | ((Some _, _), (None, _)) \<Rightarrow> False
       | ((Some l1, l2 ), (Some r1, r2)) \<Rightarrow> l1 = r1 \<and> l2 = r2)" *)
"test_lleq l r =
(case (l) of
         (None, l2) \<Rightarrow> (case r of (_, r2) \<Rightarrow> l2 = r2)
       | ((Some l1, l2)) \<Rightarrow> (case r of (None, _) \<Rightarrow> False
                                 | (Some r1, r2) \<Rightarrow> (l1 = r1 \<and> l2 = r2)))"

definition test_bsup :: "(nat option * nat) \<Rightarrow> (nat option * nat) \<Rightarrow> (nat option * nat)" where
(*
"test_bsup l r =
  (case (l, r) of
            ((None, l2), (None, r2)) \<Rightarrow> (None, l2)
            |((None, l2), (Some r1, r2)) \<Rightarrow> (Some r1, l2)
            |((Some l1, l2), (None, r2)) \<Rightarrow> (Some l1, l2)
            |((Some l1, l2), (Some r1, r2)) \<Rightarrow> (Some l1, l2))"
*)
"test_bsup l r =
  (case (l) of
         (None, l2) \<Rightarrow> (case r of (None, _) \<Rightarrow> (None, l2)
                                  | (Some r1, _) \<Rightarrow> (Some r1, l2))
       | ((Some l1, l2)) \<Rightarrow> (Some l1, l2))"

value "test_bsup (None, 1) (Some 3, 2)"

interpretation Test : Mergeable_Spec test_lleq test_bsup

  apply(unfold_locales)
  apply(simp add:test_lleq_def)
     apply(simp split:prod.splits option.splits)
  apply(simp add:test_lleq_def)
     apply(simp split:prod.splits option.splits)
  apply(simp add:test_lleq_def)
     apply(simp split:prod.splits option.splits)

  apply(simp add:Mergeable'.is_bsup_weak_def Mergeable'.is_bsup_def Mergeable'.is_bub_def LatticeLike.is_least_def LatticeLike.is_sup_def LatticeLike.is_ub_def
                 Mergeable'.is_bub_weak_def)

  apply(auto)

    apply(simp add:test_lleq_def test_bsup_def)
     apply(simp split:prod.splits option.splits)

   apply(simp add:ord_extends_def)
  apply(auto)

    apply(simp add:test_lleq_def test_bsup_def)
   apply(case_tac a; clarsimp)
apply(case_tac aa; clarsimp)

  

     apply(rotate_tac -1)
      apply(frule_tac x = None in spec)
      apply(rotate_tac -1)
  apply(drule_tac x = ba in spec)
  apply(rotate_tac -1)
      apply(drule_tac x = ab in spec)
     apply(rotate_tac -1)
      apply(drule_tac x = bb in spec)
      apply(rotate_tac -1)


     apply(auto)
  apply(case_tac ab; auto)

         apply(drule_tac x = None in spec) apply(drule_tac x = bb in spec)
  apply(auto)
                      apply(simp add:LatticeLike_Weak_Spec.leq_refl)

         apply(case_tac a; auto)
        apply(case_tac ab; auto)
        apply(case_tac aa; auto)

         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "ba" in spec) apply(rotate_tac -1)
         apply(auto)

  apply(drule_tac a = "(None, bb)" and b = "(Some a, bb)" and c = "(None, ba)"
        in LatticeLike_Weak_Spec.leq_trans) apply(auto)

            apply(case_tac aa; auto)
apply(case_tac aa; auto)

  apply(drule_tac a = "(Some a, bb)" and b = "(None, ba)" and c = "(None, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)

apply(case_tac aa; auto)
apply(case_tac aa; auto)

  apply(case_tac ab; auto)

  apply(drule_tac a = "(Some a, bb)" and b = "(None, ba)" and c = "(None, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)


  apply(drule_tac a = "(Some a, bb)" and b = "(None, ba)" and c = "(None, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)

         apply(frule_tac x = "Some ab" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "ba" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "Some a" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
         apply(auto)

apply(case_tac aa; auto)
            apply(case_tac ac; auto)


  apply(drule_tac a = "(Some a, bb)" and b = "(Some aa, bc)" and c = "(None, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)

            apply(case_tac ac; auto)

         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bc" in spec) apply(rotate_tac -1)
         apply(auto)

  apply(drule_tac a = "(None, bb)" and b = "(Some a, bb)" and c = "(None, bc)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)

  apply(case_tac ab; auto)
  apply(case_tac ab; auto)
             apply(case_tac ac; auto)

  apply(drule_tac x = None in spec) apply(drule_tac x = bb in spec) apply(auto)
                      apply(simp add:LatticeLike_Weak_Spec.leq_refl)

  apply(case_tac ab; auto)
           apply(case_tac ab; auto)

  apply(drule_tac x = None in spec) apply(drule_tac x = bb in spec) apply(auto)
                      apply(simp add:LatticeLike_Weak_Spec.leq_refl)
           
apply(case_tac aa; auto)
            apply(case_tac ac; auto)

  apply(frule_tac a = "(None, bb)" and b = "(Some a, bb)" and c = "(None, bc)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)

         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bc" in spec) apply(rotate_tac -1)
         apply(auto)

  apply(case_tac ab; auto)
  apply(case_tac ab; auto)
           apply(case_tac ac; auto)

  apply(drule_tac x = None in spec) apply(drule_tac x = bb in spec) apply(auto)
                      apply(simp add:LatticeLike_Weak_Spec.leq_refl)

  apply(drule_tac a = "(Some a, bb)" and b = "(None, bc)" and c = "(None, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)

           apply(case_tac ac; auto)

  apply(frule_tac a = "(None, bb)" and b = "(Some a, bb)" and c = "(None, bc)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)

         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bc" in spec) apply(rotate_tac -1)
         apply(auto)

  apply(case_tac ab; auto)
          apply(case_tac ab; auto)

  apply(drule_tac x = None in spec) apply(drule_tac x = bb in spec) apply(auto)
                      apply(simp add:LatticeLike_Weak_Spec.leq_refl)

apply(case_tac aa; auto)
            apply(case_tac ac; auto)
  apply(frule_tac a = "(None, bb)" and b = "(Some a, bb)" and c = "(None, bc)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)

         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bc" in spec) apply(rotate_tac -1)
         apply(auto)
          apply(case_tac ab; auto)
          apply(case_tac ab; auto)

  apply(drule_tac x = None in spec) apply(drule_tac x = bb in spec) apply(auto)
                      apply(simp add:LatticeLike_Weak_Spec.leq_refl)

         apply(case_tac ac; auto)


  apply(frule_tac a = "(None, bb)" and b = "(Some a, bb)" and c = "(None, bc)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)

         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bc" in spec) apply(rotate_tac -1)
         apply(auto)

  apply(case_tac ab; auto)
          apply(case_tac ab; auto)

  apply(drule_tac x = None in spec) apply(drule_tac x = bb in spec) apply(auto)
                      apply(simp add:LatticeLike_Weak_Spec.leq_refl)

apply(case_tac aa; auto)
            apply(case_tac ac; auto)
  apply(frule_tac a = "(None, bb)" and b = "(Some a, bb)" and c = "(None, bc)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)

         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bc" in spec) apply(rotate_tac -1)
         apply(auto)
          apply(case_tac ab; auto)
          apply(case_tac ab; auto)

  apply(drule_tac x = None in spec) apply(drule_tac x = bb in spec) apply(auto)
                      apply(simp add:LatticeLike_Weak_Spec.leq_refl)

            apply(case_tac ac; auto)


  apply(frule_tac a = "(None, bb)" and b = "(Some a, bb)" and c = "(None, bc)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)

         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bc" in spec) apply(rotate_tac -1)
         apply(auto)

  apply(case_tac ab; auto)
          apply(case_tac ab; auto)

  apply(drule_tac x = None in spec) apply(drule_tac x = bb in spec) apply(auto)
                      apply(simp add:LatticeLike_Weak_Spec.leq_refl)

       apply(case_tac a; auto)

        apply(rotate_tac 1)
        apply(drule_tac x = None in spec) apply(rotate_tac -1)
  apply(drule_tac x = ba in spec) apply(auto)
                      apply(simp add:LatticeLike_Weak_Spec.leq_refl)

  apply(frule_tac a = "(ab, bb)" and b = "(None, ba)" and c = "(None, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)

       apply(case_tac ab; auto)

  apply(frule_tac a = "(None, bb)" and b = "(Some a, bb)" and c = "(None, ba)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)

         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "ba" in spec) apply(rotate_tac -1)
         apply(auto)
          apply(case_tac ab; auto)
          apply(case_tac ab; auto)

  apply(drule_tac x = None in spec) apply(drule_tac x = bb in spec) apply(auto)
                      apply(simp add:LatticeLike_Weak_Spec.leq_refl)



       apply(case_tac a; auto)
          apply(case_tac ab; auto)

  apply(frule_tac a = "(None, bb)" and b = "(Some a, bb)" and c = "(None, ba)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)


         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "ba" in spec) apply(rotate_tac -1)
      apply(auto)
                      apply(simp add:LatticeLike_Weak_Spec.leq_refl)

          apply(case_tac ab; auto)
          apply(case_tac ab; auto)


  apply(frule_tac a = "(Some a, bb)" and b = "(None, ba)" and c = "(None, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)

(* 4 goals! *)

       apply(case_tac a; auto)
          apply(case_tac ab; auto)

  apply(rotate_tac 1)
      apply(drule_tac x = None in spec) apply(rotate_tac -1)
  apply(drule_tac x = bb in spec) apply(auto)
                      apply(simp add:LatticeLike_Weak_Spec.leq_refl)

          apply(case_tac ab; auto)


  apply(frule_tac a = "(None, bb)" and b = "(Some a, bb)" and c = "(None, ba)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)


         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "ba" in spec) apply(rotate_tac -1)
      apply(auto)
                      apply(simp add:LatticeLike_Weak_Spec.leq_refl)

          apply(case_tac ab; auto)
          apply(case_tac ab; auto)

      apply(drule_tac x = None in spec) apply(rotate_tac -1)
  apply(drule_tac x = bb in spec) apply(auto)
     apply(simp add:LatticeLike_Weak_Spec.leq_refl)


(* is this where we go off the rails? *)

(*
    apply(case_tac ab; auto)
     apply(drule_tac a = "(None, bb)" and b = "(Some a, bb)" in ord_leq') apply(simp add:test_lleq_def)
  apply(simp)
*)
(*
    apply(drule_tac x = "(Some a)" in spec) apply(rotate_tac -1)
    apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
    apply(auto)
*)

(*
     apply(drule_tac a = "(None, bb)" and b = "(Some a, bb)" in ord_leq') apply(simp add:test_lleq_def)
  apply(simp)
*)

        apply(case_tac ab; auto)

  defer


    apply(rotate_tac -1)
         apply(frule_tac x = "Some a" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "ba" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "Some aa" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
      apply(auto)

        apply(case_tac ab; auto)

         apply(case_tac ac; auto)

         defer

         apply(case_tac ac; auto)
  apply(rotate_tac 1)
         apply(drule_tac x = "Some ab" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
  apply(auto)
         apply(drule_tac x = "Some ab" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bc" in spec) apply(rotate_tac -1)
         apply(auto)
         apply(case_tac a; auto)
             apply(case_tac ac; auto)

  defer

             apply(case_tac ac; auto)


  apply(frule_tac a = "(ab, bb)" and b = "(Some aa, bc)" and c = "(None, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(simp)
          apply(simp)


  apply(frule_tac a = "(ab, bb)" and b  = "(None, bb)" and c = "(Some aa, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(simp)
            apply(frule_tac a = "(None, bb)" and b = "(Some aa, bb)" in ord_leq')
          apply(simp add:test_lleq_def) apply(simp) apply(simp)

       apply(case_tac ac; auto)
        apply(case_tac ab; auto)



  apply(frule_tac a = "(None, bb)" and b  = "(Some a, bb)" and c = "(Some aa, bc)" in
    LatticeLike_Weak_Spec.leq_trans) apply(simp) apply(simp)


    apply(rotate_tac -1)
         apply(frule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "Some aa" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bc" in spec) apply(rotate_tac -1)
       apply(auto)

          apply(case_tac ab; auto)
          defer
   apply(case_tac ab; auto)
           apply(case_tac ac; auto)

  defer

  apply(frule_tac a = "(Some aa, bb)" and c  = "(None, bb)" and b = "(Some ab, bc)" in
    LatticeLike_Weak_Spec.leq_trans) 
             apply(simp) apply(simp)
  apply(frule_tac a = "(Some aa, bb)" and b  = "(None, bb)" and c = "(Some ab, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(simp)

            apply(drule_tac a = "(None, bb)" and b = "(Some ab, bb)" in ord_leq')
             apply(simp add:test_lleq_def) apply(simp) apply(simp)


  apply(frule_tac a = "(Some aa, bb)" and c  = "(None, bb)" and b = "(Some ab, bc)" in
    LatticeLike_Weak_Spec.leq_trans) 
             apply(simp) apply(simp)
  apply(frule_tac a = "(Some aa, bb)" and b  = "(None, bb)" and c = "(Some ab, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(simp)

            apply(drule_tac a = "(None, bb)" and b = "(Some ab, bb)" in ord_leq')
             apply(simp add:test_lleq_def) apply(simp) apply(simp)

          apply(case_tac a; auto)
          apply(case_tac ac; auto)

  apply(frule_tac a = "(Some aa, bb)" and c  = "(None, bb)" and b = "(Some ab, bc)" in
    LatticeLike_Weak_Spec.leq_trans) 
             apply(simp) apply(simp)
  apply(frule_tac a = "(Some aa, bb)" and b  = "(None, bb)" and c = "(Some ab, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(simp)

            apply(drule_tac a = "(None, bb)" and b = "(Some ab, bb)" in ord_leq')
             apply(simp add:test_lleq_def) apply(simp) apply(simp)


         apply(frule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "Some a" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "ba" in spec) apply(rotate_tac -1)
       apply(auto)



             apply(case_tac ab; auto)
  apply(case_tac ac; auto)


  apply(frule_tac a = "(Some aa, bb)" and b = "(Some a, ba)" and c = "(None, bb)" in
    LatticeLike_Weak_Spec.leq_trans) 
             apply(simp) apply(simp)
  apply(frule_tac a = "(Some aa, bb)" and b  = "(None, bb)" and c = "(Some a, bb)" in
    LatticeLike_Weak_Spec.leq_trans) 
          apply(simp)
            apply(drule_tac a = "(None, bb)" and b = "(Some a, bb)" in ord_leq')
          apply(simp add:test_lleq_def) apply(simp) apply(simp)



  apply(frule_tac a = "(Some aa, bb)" and b = "(Some a, ba)" and c = "(None, bb)" in
    LatticeLike_Weak_Spec.leq_trans) 
             apply(simp) apply(simp)
  apply(frule_tac a = "(Some aa, bb)" and b  = "(None, bb)" and c = "(Some a, bb)" in
    LatticeLike_Weak_Spec.leq_trans) 
          apply(simp)
            apply(drule_tac a = "(None, bb)" and b = "(Some a, bb)" in ord_leq')
          apply(simp add:test_lleq_def) apply(simp) apply(simp)

             apply(case_tac ab; auto)
  apply(case_tac ac; auto)



  apply(frule_tac a = "(Some aa, bb)" and b = "(Some a, ba)" and c = "(None, bb)" in
    LatticeLike_Weak_Spec.leq_trans) 
             apply(simp) apply(simp)
  apply(frule_tac a = "(Some aa, bb)" and b  = "(None, bb)" and c = "(Some a, bb)" in
    LatticeLike_Weak_Spec.leq_trans) 
          apply(simp)
            apply(drule_tac a = "(None, bb)" and b = "(Some a, bb)" in ord_leq')
          apply(simp add:test_lleq_def) apply(simp) apply(simp)


  apply(frule_tac a = "(Some aa, bb)" and b = "(Some ab, bc)" and c = "(None, bb)" in
    LatticeLike_Weak_Spec.leq_trans) 
             apply(simp) apply(simp)
  apply(frule_tac a = "(Some aa, bb)" and b  = "(None, bb)" and c = "(Some ab, bb)" in
    LatticeLike_Weak_Spec.leq_trans) 
          apply(simp)
            apply(drule_tac a = "(None, bb)" and b = "(Some ab, bb)" in ord_leq')
          apply(simp add:test_lleq_def) apply(simp) apply(simp)

          apply(rotate_tac 2)
          apply(frule_tac x = "Some a" in spec) apply(rotate_tac -1)
apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
          apply(auto)

            apply(drule_tac a = "(None, bb)" and b = "(Some a, bb)" in ord_leq')
          apply(simp add:test_lleq_def) apply(simp)

  apply(frule_tac a = "(Some a, ba)" and b = "(None, bb)" and c = "(Some a, bb)" in
    LatticeLike_Weak_Spec.leq_trans) 
          apply(simp)
            apply(drule_tac a = "(None, bb)" and b = "(Some a, bb)" in ord_leq')
          apply(simp add:test_lleq_def) apply(simp)


  apply(frule_tac a = "(None, bb)" and b = "(Some aa, bb)" and c = "(Some aa, bc)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)


    apply(rotate_tac -1)
         apply(frule_tac x = "Some aa" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bc" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
            apply(auto)



  apply(case_tac ab; auto)

 apply(case_tac ac; auto)

  apply(frule_tac a = "(Some a, bb)" and b = "(Some ab, ba)" and c = "(None, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)

  apply(frule_tac a = "(Some a, bb)" and b = "(None, bb)" and c = "(Some ab, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)
           apply(frule_tac a = "(None, bb)" and b = "(Some ab, bb)" in ord_leq') apply(auto)
           apply(simp add:test_lleq_def)


  apply(case_tac ab; auto)

 apply(case_tac ac; auto)


  apply(frule_tac a = "(Some a, bb)" and b = "(Some ab, ba)" and c = "(None, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)

  apply(frule_tac a = "(Some a, bb)" and b = "(None, bb)" and c = "(Some ab, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)
           apply(frule_tac a = "(None, bb)" and b = "(Some ab, bb)" in ord_leq') apply(auto)
           apply(simp add:test_lleq_def)


  apply(case_tac ab; auto)

 apply(case_tac ac; auto)


  apply(frule_tac a = "(Some a, bb)" and b = "(Some ab, ba)" and c = "(None, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)

  apply(frule_tac a = "(Some a, bb)" and b = "(None, bb)" and c = "(Some ab, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)
           apply(frule_tac a = "(None, bb)" and b = "(Some ab, bb)" in ord_leq') apply(auto)
         apply(simp add:test_lleq_def)

  apply(case_tac ab; auto)

 apply(case_tac ac; auto)


  apply(frule_tac a = "(Some a, bb)" and b = "(Some ab, ba)" and c = "(None, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)

  apply(frule_tac a = "(Some a, bb)" and b = "(None, bb)" and c = "(Some ab, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)
           apply(frule_tac a = "(None, bb)" and b = "(Some ab, bb)" in ord_leq') apply(auto)
        apply(simp add:test_lleq_def)

  apply(case_tac ab; auto)

       apply(case_tac ac; auto)

(* you are here. below is chasing my tail i think *)

  apply(frule_tac a = "(None, bb)" and b = "(Some aa, bb)" and c = "(Some ab, bc)"  in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)


       apply(frule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "Some ab" in spec) apply(rotate_tac -1)
       apply(drule_tac x = "bc" in spec) apply(rotate_tac -1)
 
        apply(auto)
  apply(case_tac a; auto)
           apply(case_tac ac; auto)
           defer (* transitivity *)
  defer (* trans *)
           apply(case_tac a; auto)
           apply(case_tac ac; auto)
             defer


       apply(frule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "Some ab" in spec) apply(rotate_tac -1)
       apply(drule_tac x = "bc" in spec) apply(rotate_tac -1)
  apply(auto)

           apply(case_tac ac; auto)
              defer

              apply(case_tac ac; auto)

apply(case_tac ad; auto) defer

         apply(drule_tac x = "Some a" in spec) apply(rotate_tac -1)
       apply(drule_tac x = "b" in spec) apply(rotate_tac -1)
        apply(frule_tac x = "Some ab" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bc" in spec) apply(rotate_tac -1)

           defer (* transitivity *)

  apply(case_tac a; auto)
           apply(case_tac ac; auto)

           defer (* transitivity *)

           apply(case_tac ac; auto)


  apply(rotate_tac 1)
       apply(drule_tac x = "Some ab" in spec) apply(rotate_tac -1) apply(drule_tac x = bb in spec)
       apply(auto)

  defer


  apply(rotate_tac -1)
         apply(frule_tac x = "Some ab" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bc" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "Some aa" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
        apply(auto)
  apply(case_tac a; auto)
           apply(case_tac ac; auto)
           defer (* transitivity *)
           apply(case_tac ac; auto)

         apply(frule_tac x = "Some a" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "ba" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "Some aa" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
           apply(auto)

  apply(case_tac ab; auto)
               apply(case_tac ac; auto)
               defer (* transitivity *)
               apply(case_tac ac; auto)

(* this bit seemed promising *)

         apply(frule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "Some ab" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bc" in spec) apply(rotate_tac -1)
        apply(auto)

           defer (* transitivity *)

  apply(case_tac a; auto)

  defer (* transitivity *)

  apply(case_tac a; auto)
            apply(case_tac ac; auto)

  defer (* transitivity *)

         apply(frule_tac x = "Some ab" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bc" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "Some aa" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
        apply(auto)

(* end promising bit *)
  apply(case_tac a; auto)

 apply(case_tac ac; auto)

  apply(frule_tac a = "(Some a, ba)" and b = "(None, bb)" and c = "(Some a, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)

            apply(drule_tac a = "(None, bb)" and b = "(Some a, bb)" in ord_leq') apply(auto)
  apply(simp add:test_lleq_def)

  apply(frule_tac a = "(Some aa, bb)" and b = "(Some a, ba)" and c = "(None, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)


  apply(frule_tac a = "(Some aa, bb)" and b = "(None, bb)" and c = "(Some a, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)

            apply(drule_tac a = "(None, bb)" and b = "(Some a, bb)" in ord_leq') apply(auto)
  apply(simp add:test_lleq_def)

 apply(case_tac ac; auto)

          apply(rotate_tac 1)
          apply(drule_tac x = "Some a" in spec) apply(rotate_tac -1)
          apply(drule_tac x = bb in spec) apply(auto)


            apply(drule_tac a = "(None, bb)" and b = "(Some a, bb)" in ord_leq') apply(auto)
  apply(simp add:test_lleq_def)

         apply(frule_tac x = "Some a" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "ba" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "Some aa" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
          apply(auto)

  apply(case_tac ab; auto)

       apply(case_tac ac; auto)
              defer

       apply(case_tac ac; auto)


         apply(frule_tac x = "Some ab" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bc" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "Some aa" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
          apply(auto)

                 apply(case_tac a; auto)
 apply(case_tac ac; auto)

                  defer

 apply(case_tac ac; auto)


(* you are here? *)

         apply(frule_tac x = "Some a" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "ba" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "Some aa" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
           apply(auto)


  apply(case_tac ab; auto)

                apply(case_tac ac; auto)

  apply(frule_tac a = "(Some ab, bc)" and b = "(None, bb)" and c = "(Some ab, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto) defer (*easy*)



                apply(case_tac ac; auto)

         apply(frule_tac x = "Some ab" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bc" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "Some aa" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
           apply(auto)


  apply(case_tac a; auto)

                    apply(case_tac ac; auto)

  apply(frule_tac a = "(Some a, ba)" and b = "(None, bb)" and c = "(Some a, bb)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto) defer (*easy*)

                    apply(case_tac ac; auto)


  apply(frule_tac a = "(None, bb)" and b = "(Some a, bb)" and c = "(Some aa, bc)" in
    LatticeLike_Weak_Spec.leq_trans) apply(auto)

         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "bb" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "None" in spec) apply(rotate_tac -1)
         apply(drule_tac x = "ba" in spec) apply(rotate_tac -1)
         apply(auto)
          apply(case_tac ab; auto)
          apply(case_tac ab; auto)

  apply(drule_tac x = None in spec) apply(drule_tac x = bb in spec) apply(auto)
                      apply(simp add:LatticeLike_Weak_Spec.leq_refl)


            apply(case_tac ac; auto)

      apply(rotate_tac -1)
   apply(drule_tac x = bb in spec)
      apply(drule_tac x = a in spec)
      apply(rotate_tac -1)
      apply(drule_tac x = b in spec)
      apply(rotate_tac -1)
      apply(drule_tac x = ab in spec)
      apply(rotate_tac -1)
   apply(drule_tac x = bb in spec)

   apply(clarsimp)

   apply(drule_tac R = "lleq' (ab, bb) (test_bsup (a, b) (aa, ba))" in HOL.disjE)
     apply(drule_tac R = "lleq' (ab, bb) (test_bsup (a, b) (aa, ba))" in HOL.disjE)

    apply(simp add:test_lleq_def test_bsup_def)
     apply(simp split:prod.splits option.splits)
  apply(clarsimp)

  apply(case_tac x1a; clarsimp)

      apply(drule_tac x = None in spec)
      apply(rotate_tac -1)
                      apply(drule_tac x = x2a in spec) apply(clarsimp)
                      apply(simp add:LatticeLike_Weak_Spec.leq_refl)

      apply(simp add:test_lleq_def test_bsup_def)
      apply(case_tac aa; clarsimp)
       apply(case_tac a; clarsimp)
apply(case_tac ac; clarsimp)
         apply(drule_tac x = None in spec) apply(drule_tac x = bd in spec) apply(clarsimp)
                      apply(simp add:LatticeLike_Weak_Spec.leq_refl)
apply(case_tac ab; clarsimp)
apply(case_tac ac; clarsimp)
apply(case_tac ad; clarsimp)
       apply(case_tac ab; clarsimp)

       apply(case_tac a; clarsimp)
apply(case_tac ad; clarsimp)
        apply(case_tac ab; clarsimp)
  apply(case_tac ae; clarsimp)

  apply(frule_tac a = and b = and c = in LatticeLike_Weak_Spec.leq_trans)
apply(case_tac ac; clarsimp)
apply(case_tac ad; clarsimp)
apply(case_tac ab; clarsimp)

     apply(simp split:prod.splits option.splits)
        apply(clarsimp)
  apply(case_tac x1a; clarsimp)

      apply(drule_tac x = None in spec)
      apply(rotate_tac -1)
   apply(drule_tac x = x2b in spec)

        apply(clarsimp)
                      apply(simp add:LatticeLike_Weak_Spec.leq_refl)

  apply(clarsimp)

       apply(case_tac x1b; clarsimp)

        apply(frule_tac a = "(Some x2d, x2a)" and b = "(None, x2b)" and c = "(Some x2d, x2b)" in LatticeLike_Weak_Spec.leq_trans)
  apply(simp) apply(drule_tac a = "(None, x2b)" and b = "(Some x2d, x2b)" in ord_leq')
          apply(simp add:test_lleq_def) apply(simp) apply(clarsimp)
  apply(simp)
  apply(safe)

                      apply(simp split:option.splits) apply(clarsimp)
                      apply(drule_tac x = None in spec) apply(drule_tac x = bb in spec)
  apply(auto)
apply(simp add:LatticeLike_Weak_Spec.leq_refl)
                      apply(simp split:option.splits) apply(clarsimp)
                      apply(drule_tac a = "(None, bb)" and b = "(Some x2a, bb)" in ord_leq')
                      apply(simp add:test_lleq_def) apply(simp)

                      apply(auto)
  apply(drule_tac x = "None" in spec) apply(drule_tac x = "bb" in spec)
                      apply(auto)
apply(simp add:LatticeLike_Weak_Spec.leq_refl)


(*
apply(case_tac aa; auto)

    
      apply(rotate_tac -1)
      apply(frule_tac x = None in spec)
      apply(rotate_tac -1)
      apply(drule_tac x = b in spec)
      apply(rotate_tac -1)
      apply(drule_tac x = ab in spec)
      apply(rotate_tac -1)
  apply(drule_tac x = bb in spec)

     apply(simp add:test_lleq_def)

  apply(case_tac ab; auto)
   apply(case_tac a; auto)
   apply(case_tac a; auto)
   apply(case_tac a; auto)
          apply(case_tac a; auto)

      apply(rotate_tac -1)
      apply(frule_tac x = None in spec)
      apply(rotate_tac -1)
      apply(drule_tac x = ba in spec)
      apply(rotate_tac -1)
      apply(drule_tac x = "Some a" in spec)
      apply(rotate_tac -1)
  apply(drule_tac x = bb in spec)

         apply(auto)
  apply(rotate_tac -1)
  apply(drule_tac x = None in spec) 
             apply(drule_tac x = bb in spec)
  apply(auto)
             apply(simp add:LatticeLike_Weak_Spec.leq_refl)

            apply(case_tac aa; auto)
            apply(case_tac ab; auto)

             apply(drule_tac x = None in spec) apply(rotate_tac -1)
             apply(drule_tac x = bc in spec)
             apply(rotate_tac -1)
             apply(drule_tac x = "Some a" in spec) apply(rotate_tac -1)
             apply(drule_tac x = bb in spec)

             apply(auto)
            apply(case_tac aa; auto)
            apply(case_tac ab; auto)


      apply(rotate_tac -1)
      apply(drule_tac x = None in spec)
      apply(rotate_tac -1)
                 apply(drule_tac x = ba in spec)
  apply(auto)
      apply(rotate_tac -1)
      apply(drule_tac x = ab in spec)
      apply(rotate_tac -1)
  apply(drule_tac x = bb in spec)

     apply(simp split:prod.splits option.splits)

  apply(drule_tac x = None in spec) apply(drule_tac x = bb in spec) apply(clarsimp)
              apply(drule_tac a = "(None, bb)" in LatticeLike_Weak_Spec.leq_refl) apply(simp)

  apply(clarsimp) apply(safe)


      apply(rotate_tac -1)
      apply(drule_tac x = None in spec)
      apply(rotate_tac -1)
      apply(drule_tac x = b in spec)
      apply(rotate_tac -1)
      apply(drule_tac x = None in spec)
      apply(rotate_tac -1)
  apply(drule_tac x = bb in spec) apply(auto)

           apply(simp add:test_lleq_def split:prod.splits option.splits; clarsimp)
          apply(simp add:test_lleq_def split:prod.splits option.splits; clarsimp)
         apply(simp add:test_lleq_def split:prod.splits option.splits; clarsimp)
        apply(simp add:test_lleq_def split:prod.splits option.splits; clarsimp)
       apply(simp add:test_lleq_def split:prod.splits option.splits; clarsimp)


      apply(rotate_tac -1)
      apply(frule_tac x = None in spec)
      apply(rotate_tac -1)
      apply(drule_tac x = b in spec)
      apply(rotate_tac -1)
      apply(drule_tac x = "Some a" in spec)
      apply(rotate_tac -1)
  apply(drule_tac x = bb in spec) apply(clarify) apply(safe)

          apply(simp add:test_lleq_def; clarsimp)

      apply(drule_tac x = None in spec)
      apply(rotate_tac -1)
      apply(drule_tac x = ba in spec)
      apply(rotate_tac -1)
      apply(drule_tac x = "Some a" in spec)
      apply(rotate_tac -1)
          apply(drule_tac x = bb in spec) apply(clarify) apply(safe)
              apply(auto)

              apply(drule_tac x = None in spec) apply(drule_tac x = bb in spec) apply(auto)
  apply(drule_tac a = "(None, bb)" and b = "(None, bb)" in ord_leq') apply(auto)
  
          apply(simp add:test_lleq_def split:prod.splits option.splits; clarsimp)
         apply(simp add:test_lleq_def split:prod.splits option.splits; clarsimp)
        apply(simp add:test_lleq_def split:prod.splits option.splits; clarsimp)
       apply(simp add:test_lleq_def split:prod.splits option.splits; clarsimp)


         apply(simp split:prod.splits option.splits)
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
*)
end