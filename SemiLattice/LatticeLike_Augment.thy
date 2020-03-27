theory LatticeLike_Augment imports Main

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
  LatticeLike +
  fixes aug_leq :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  fixes aug :: "'a \<Rightarrow> 'b"
  fixes deaug :: "'b \<Rightarrow> 'a option"
  

begin


definition is_bub :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bub a b s =
  (lleq a s \<and>
    ((\<forall> bd sd . aug_leq bd (aug b) \<longrightarrow>
                LatticeLike.is_sup aug_leq {aug a, bd} sd \<longrightarrow>
                aug_leq sd (aug s))))"

definition is_bsup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bsup a b s =
  is_least (is_bub a b) s"

end

locale Mergeable =
  Mergeable' +
  fixes bsup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

locale Mergeable_Spec' =
  Mergeable +
  LatticeLike_Spec +
  LLaug : LatticeLike_Spec aug_leq + 
  (* TODO: maybe this can be proven from fewer assumptions *)

assumes aug_deaug :
  "\<And> a . deaug (aug a) = Some a"
assumes deaug_aug :
  "\<And> b a . deaug b = Some a \<Longrightarrow> aug a = b"

assumes leq_aug_leq :
  "\<And> a a'. lleq a a' \<Longrightarrow>  aug_leq (aug a) (aug a')"

assumes aug_leq_leq1 :
  "\<And> b b' a . aug_leq b b' \<Longrightarrow>
              deaug b = Some a \<Longrightarrow> 
              (\<exists> a' . deaug b' = Some a' \<and> lleq a a')"

assumes aug_leq_leq2 :
  "\<And> b b' . aug_leq b b' \<Longrightarrow>
              deaug b' = None \<Longrightarrow> 
              deaug b = None"
(*
(* this one seems odd/perhaps insufficient *)
assumes aug_leq_connected :
  "\<And> b . deaug b = None \<Longrightarrow>
         (\<exists> b' a . deaug b' = Some a \<and> aug_leq b b')"

assumes aug_leq_connected2 :
  "\<And> b' . deaug b' = Some a' \<Longrightarrow>
           (\<exists> b . deaug b = None \<and> aug_leq b b')"
*)
assumes aug_leq_refl_none :
  "\<And> a .
    deaug a = None \<Longrightarrow> aug_leq a a"
      

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

(*
sublocale Mergeable_Spec' \<subseteq> LLaug : LatticeLike_Spec aug_leq
  apply(unfold_locales)
    apply(case_tac "deaug a")  
     apply(simp add:aug_leq_refl_none)
    apply(drule_tac deaug_aug) apply(clarsimp) apply(rule_tac leq_aug_leq) apply(simp add:leq_refl)

   apply(case_tac "deaug a")
  apply(drule_tac aug_leq_connected) apply(auto)
*)
locale Mergeable_Spec = Mergeable_Spec'
begin


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
  apply(simp add: has_sup_def is_sup_def is_bsup_def is_bub_def is_ub_def is_least_def
        LatticeLike.is_ub_def
        LatticeLike.is_sup_def LatticeLike.is_least_def is_greatest_def) apply(auto)

   apply(drule_tac x = s in spec) apply(auto)
    apply(drule_tac x = bd in spec) apply(auto)
    apply(drule_tac x = "aug s" in spec) apply(auto)
     apply(drule_tac a = a and a' = s in "leq_aug_leq") apply(auto)
  apply(drule_tac a = bd and b = "aug b" and c = "aug s"
        in LLaug.leq_trans)
     apply(rule_tac leq_aug_leq) apply(auto)

   apply(drule_tac x = "aug b" in spec) apply(auto)
    apply(simp add: LLaug.leq_refl)

  apply(drule_tac x = "aug s" in spec) apply(auto)
     apply(rule_tac leq_aug_leq) apply(auto)
     apply(rule_tac leq_aug_leq) apply(auto)

    apply(cut_tac a = a in aug_deaug)
    apply(drule_tac aug_leq_leq1) apply(simp) apply(clarsimp)

    apply(cut_tac a = b in aug_deaug)
    apply(drule_tac aug_leq_leq1) apply(simp) apply(clarsimp)
    apply(drule_tac x = a'a in spec) apply(auto)
    apply(drule_tac b = a' in deaug_aug) apply(clarsimp)
    apply(rule_tac leq_aug_leq, auto)

  apply(cut_tac a = s in aug_deaug)
   apply(drule_tac aug_leq_leq1) apply(simp) apply(clarsimp)
   apply(simp add:aug_deaug) apply(clarsimp)
   apply(drule_tac a = b and b = s and c = "bsup a b" in leq_trans) apply(auto)

  apply(drule_tac x = s in spec) apply(auto)
  apply(rotate_tac -1)
  apply(drule_tac x = "aug s" in spec) apply(auto)
    apply(simp add:leq_aug_leq)
   apply(drule_tac a = b and a' = s in leq_aug_leq) 
  apply(drule_tac a = bd and b = "aug b" and c = "aug s" in
    LLaug.leq_trans) apply(auto)

  apply(drule_tac x = a' in spec) apply(auto)
  apply(drule_tac a = "bsup a b" and b = "s" and c = a' in leq_trans) apply(auto)
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

fun test0_aug_lleq :: "nat option \<Rightarrow> nat option \<Rightarrow> bool" where
"test0_aug_lleq None _ = True"
| "test0_aug_lleq x y = (x = y)"

fun test0_bsup :: "nat option \<Rightarrow> nat option \<Rightarrow> nat option" where
"test0_bsup None r = r"
| "test0_bsup l r = l"
  

value "test0_bsup None (Some 2)"
value "test0_bsup (Some 2) (None)"
term "Mergeable_Spec"

interpretation Test0 : Mergeable_Spec test0_lleq  test0_aug_lleq id Some test0_bsup
  apply(unfold_locales)
     apply(case_tac a; clarsimp) 
    apply(case_tac a; clarsimp)
   apply(case_tac a; clarsimp)
              apply(case_tac b; clarsimp)


     apply(case_tac a; clarsimp) 
    apply(case_tac a; clarsimp)
   apply(case_tac a; clarsimp)
           apply(case_tac b; clarsimp)

  apply(auto)

     apply(case_tac a; clarsimp) 
     apply(case_tac a; clarsimp) 

  apply(simp add: Mergeable'.is_bsup_def Mergeable'.is_bub_def LatticeLike.is_least_def LatticeLike.is_sup_def LatticeLike.is_ub_def)
  
  apply(auto)
   apply(case_tac a; clarsimp)
   apply(case_tac a; clarsimp) 

   apply(case_tac a; clarsimp) 

  apply(case_tac b; clarsimp)
  apply(drule_tac x = "Some a" in spec) apply(auto)
  done


type_synonym t1 = "nat option * nat"

type_synonym t1a = "nat option * nat option"

definition test_lleq :: "t1 \<Rightarrow> t1 \<Rightarrow> bool" where 
"test_lleq l r =    (case (l, r) of
         ((None, l2), (None, r2)) \<Rightarrow> l2 = r2
       | ((None, l2), (Some r1, r2)) \<Rightarrow> l2 = r2
       | ((Some _, _), (None, _)) \<Rightarrow> False
       | ((Some l1, l2 ), (Some r1, r2)) \<Rightarrow> l1 = r1 \<and> l2 = r2)"

definition test_aug_lleq :: "t1a \<Rightarrow> t1a \<Rightarrow> bool" where 
"test_aug_lleq l r = 
   (case (l, r) of
         ((None, None), (_, _)) \<Rightarrow> True
         | ((None, Some x2), (_, Some y2)) \<Rightarrow> x2 = y2
         | ((Some x1, None), (Some y1, _)) \<Rightarrow> x1 = y1
         | ((Some x1, Some x2), (Some y1, Some y2)) \<Rightarrow> x1 = y1 \<and> x2 = y2
         | (_, _) \<Rightarrow> False)"

definition test_bsup :: "t1 \<Rightarrow> t1 \<Rightarrow> t1" where
"test_bsup = (\<lambda> l r .
    (case (l, r) of
            ((None, l2), (None, r2)) \<Rightarrow> (None, l2)
            |((None, l2), (Some r1, r2)) \<Rightarrow> (Some r1, l2)
            |((Some l1, l2), (None, r2)) \<Rightarrow> (Some l1, l2)
            |((Some l1, l2), (Some r1, r2)) \<Rightarrow> (Some l1, l2)))"

definition test_aug :: "t1 \<Rightarrow> t1a" where
"test_aug t =
  (case t of
    (x1, x2) \<Rightarrow> (x1, Some x2))"

definition test_deaug :: "t1a \<Rightarrow> t1 option" where
"test_deaug ta =
  (case ta of
    (x1, Some x2) \<Rightarrow> Some (x1, x2)
    | _ \<Rightarrow> None)"


interpretation Test : Mergeable_Spec test_lleq test_aug_lleq test_aug test_deaug test_bsup

  apply(unfold_locales)
              apply(simp add:test_aug_lleq_def test_lleq_def split:prod.splits option.splits)
  apply(simp add:test_aug_lleq_def test_lleq_def split:prod.splits option.splits)
            apply(simp add:test_aug_lleq_def test_lleq_def split:prod.splits option.splits)
           apply(simp add:test_aug_lleq_def test_lleq_def split:prod.splits option.splits)
          apply(simp add:test_aug_lleq_def test_lleq_def split:prod.splits option.splits)
         apply(simp add:test_aug_lleq_def test_lleq_def split:prod.splits option.splits)
        apply(simp add:test_aug_def test_deaug_def split:prod.splits option.splits)
       apply(simp add:test_aug_def test_deaug_def split:prod.splits option.splits)
       apply(clarsimp)

      apply(simp add:test_aug_lleq_def test_lleq_def test_aug_def test_deaug_def split:prod.splits option.splits)

      apply(simp add:test_aug_lleq_def test_lleq_def test_aug_def test_deaug_def split:prod.splits option.splits)
      apply(clarsimp) apply(fastforce)
apply(clarsimp) apply(fastforce)
     apply(simp add:test_aug_lleq_def test_lleq_def test_aug_def test_deaug_def split:prod.splits option.splits)
   apply(simp add:test_aug_lleq_def test_lleq_def test_aug_def test_deaug_def split:prod.splits option.splits)

  apply(simp add: Mergeable'.is_bsup_def Mergeable'.is_bub_def LatticeLike.is_least_def LatticeLike.is_sup_def LatticeLike.is_ub_def)
  apply(simp add:test_aug_lleq_def test_lleq_def test_aug_def test_deaug_def test_bsup_def)
  apply(case_tac a; clarsimp)
  apply(case_tac aaa; clarsimp)
   apply(case_tac aa; clarsimp)
  apply(case_tac a; clarsimp)
    apply(case_tac b; clarsimp)
      apply(case_tac bb; clarsimp)
      apply(case_tac ab; clarsimp) 
       apply(drule_tac x = None in spec) apply(drule_tac x = "Some a" in spec)
        apply(clarsimp)

  apply(case_tac bb; clarsimp)
       apply(case_tac ab; clarsimp) 

       apply(drule_tac x = None in spec) apply(drule_tac x = "Some a" in spec)
        apply(clarsimp)

  apply(case_tac bb; clarsimp)
       apply(case_tac ab; clarsimp) 
    apply(case_tac b; clarsimp)

  apply(auto)

      apply(case_tac aa; clarsimp)
    apply(case_tac b; clarsimp)
    apply(case_tac bb; clarsimp)

      apply(case_tac ab; clarsimp) 
       apply(drule_tac x = "None"  in spec) apply(drule_tac x = "Some aa" in spec)
        apply(clarsimp)

       apply(case_tac ab; clarsimp)
    apply(case_tac bb; clarsimp)
    apply(case_tac bb; clarsimp)
       apply(drule_tac x = "None"  in spec) apply(drule_tac x = "Some ab" in spec)
       apply(clarsimp)

      apply(case_tac b; clarsimp)
    apply(case_tac bb; clarsimp)
       apply(case_tac ab; clarsimp)
       apply(case_tac ab; clarsimp)
      apply(case_tac bb; clarsimp)

  apply(simp cong:option.case_cong)
  apply(case_tac aa; clarsimp)
  apply(simp cong:option.case_cong)

       apply(drule_tac x = "Some a" in spec) apply(auto)
       apply(drule_tac x = "None" in spec)
       apply(auto)

       apply(drule_tac x = "Some a" in spec) apply(drule_tac x = "Some b" in spec)
      apply(clarsimp)
  apply(case_tac ba; auto) apply(case_tac aa; auto)

       apply(drule_tac x = "Some a" in spec) apply(auto)
       apply(drule_tac x = "None" in spec)
       apply(auto)

       apply(drule_tac x = "Some a" in spec) apply(auto)
       apply(drule_tac x = "Some b" in spec)
       apply(auto)
     apply(simp split:option.splits)
    apply(simp split:option.splits)
     apply(clarsimp) apply(clarsimp)

   apply(case_tac ab; clarsimp)
    apply(case_tac b; clarsimp)
     apply(case_tac ac; clarsimp)
     apply(case_tac bb; clarsimp)
apply(case_tac aa; clarsimp)
    apply(case_tac ac; clarsimp)
     apply(case_tac bb; clarsimp)
apply(case_tac aa; clarsimp)

    apply(case_tac b; clarsimp)
     apply(case_tac ac; clarsimp)
     apply(case_tac bb; clarsimp)
apply(case_tac aa; clarsimp)
    apply(case_tac ac; clarsimp)
     apply(case_tac bb; clarsimp)
apply(case_tac aa; clarsimp)


  apply(case_tac aa; clarsimp)
  done
(* ok, so this seems to work - but is rather ugly. *)


(* TODOS:
- prove that augmented ordering is a valid partial order
- define an "interface" for blub-like functions,
and show that the blub here implements it
(is sup when sup exists is hardest part) *)
end