theory Mergeable imports Pord Aug_Pord

begin

(*
(* preliminary definitions for use in characterizing bsup *)
context Aug_Pord
begin


(* ... *)


  assumes bsup_is_bsup:
    "\<And> a b . is_bsup a b (bsup a b)"      

*)

(* mergeable is a type with an ordering, as well as a way to
  "naturally" (-ish) merge elements that may not have a LUB *)
locale Mergeable =
  Pord +
  fixes bsup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

locale Mergeable_Spec =
  Mergeable +

assumes bsup_leq : "\<And> a b . pleq a (bsup a b)"

(* this is not true, but perhaps the converse or a version with some
   negations and condition that a \<noteq> a' is true. see below. *)
(*
assumes bsup_mono1 :
  "\<And> a a' b .
      pleq a a' \<Longrightarrow>
      (pleq (bsup a b) (bsup a' b))"
*)
(* i dont think this is true in general
  e.g. suppose a' and a are incompatible, but become
       compatible once some information is overwritten by
       "more informative" information

e.g. take type color = R | B | G where
R, B incomparable, but G is greater than everything
than bsup (R, G) = G = bsup (B, G), but R and B are incomparable.
 *)

(*
assumes bsup_mono12 :
  "\<And> a a' b .
      pleq (bsup a b) (bsup a' b) \<Longrightarrow>
      pleq a a'"
*)

(* this one is probably not provable
actually now i think it is lol *)
assumes bsup_mono2 : 
  "\<And> b b' a .
      pleq b b' \<Longrightarrow>
      pleq (bsup a b) (bsup a b')"

(* this one definitely isn't true in general
   suppose a is maximal, then b and b' can be anything *)
(*
assumes bsup_mono22 :
  "\<And> b b' a .
      pleq (bsup a b) (bsup a b') \<Longrightarrow>
      pleq b b'"
*)
assumes bsup_idem :
  "\<And> a b .
    bsup a (bsup a b) = bsup a b"

(*
i have proved the following on paper:

"\<And> a b .
  bsup (bsup a b) a = bsup a b"

*)

assumes bsup_assoc :
  "\<And> a b c .
    bsup a (bsup b c) = bsup (bsup a b) c"

(* TODO: this specification is likely incomplete - we can probably say
         more about the cases where a, b have no "real" sup *)

(* if two elements have a supremum, bsup will equal it *)
(* this one is probably not provable from the other
   axioms, but perhaps we should check *)
assumes bsup_sup :
  "\<And> a b . has_sup {a, b} \<Longrightarrow> is_sup {a, b} (bsup a b)"
(*
begin

lemma bsup_sup_test
:  "\<And> a b . has_sup {a, b} \<Longrightarrow> is_sup {a, b} (bsup a b)"
  apply(simp add:has_sup_def is_sup_def is_least_def is_ub_def)
  apply(auto)
    apply(simp add:bsup_leq)

(* if there is a proof here, it will involve (bsup a s) and (bsup b s)
but i doubt it. *)
end
*)

(* next up: we need to show that
   any Aug_Pord has enough information
   to give us bsup according to the spec above. *)

locale Aug_Mergeable =
  Aug_Pord +
  fixes bsup :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"

locale Aug_Mergeable_Spec =
  Aug_Mergeable +
  Aug_Pord_Spec +

assumes bsup_spec :
  "\<And> a b . is_bsup a b (bsup a b)"

begin

lemma aug_merge_bsup_leq : 
"\<And> a b . l_pleq a (bsup a b)"
  apply(cut_tac a = a and b = b in bsup_spec)
  apply(simp add:is_sup_def l_pleq_def is_bsup_def is_bub_def Pord.is_least_def)
  done

end
sublocale Aug_Mergeable_Spec \<subseteq> PM : Mergeable_Spec l_pleq bsup
  apply(unfold_locales)

  (* bsup_leq *)
  apply(rule_tac aug_merge_bsup_leq)

(* bsup_mono2 *)
(* perhaps this one isn't true either? *)

     apply(subgoal_tac "is_bub a b (bsup a b')")
  apply(cut_tac a = a and b = b in bsup_spec)
      apply(simp add:is_least_def l_pleq_def is_bsup_def is_bub_def is_sup_def Pord.is_least_def is_ub_def)

      apply(simp add:l_pleq_def is_bsup_def is_bub_def is_sup_def )
      apply(safe)


      apply(cut_tac a = a and b = b' in bsup_spec)
      apply(simp add:is_least_def l_pleq_def is_bsup_def is_bub_def is_sup_def Pord.is_least_def is_ub_def)

      apply(cut_tac a = a and b = b in bsup_spec)
      apply(simp add:is_least_def l_pleq_def is_bsup_def is_bub_def is_sup_def Pord.is_least_def is_ub_def)
      apply(auto)

      apply(cut_tac a = a and b = b' in bsup_spec)
        apply(simp add:is_least_def l_pleq_def is_bsup_def is_bub_def is_sup_def Pord.is_least_def is_ub_def)
      apply(clarsimp)

  apply(thin_tac
" \<forall>a'. pleq (aug a) (aug a') \<and> (\<forall>bd. pleq bd (aug b') \<longrightarrow> (\<forall>sd. pleq (aug a) sd \<and> pleq bd sd \<and> (\<forall>a'. pleq (aug a) a' \<and> pleq bd a' \<longrightarrow> pleq sd a') \<longrightarrow> pleq sd (aug a'))) \<longrightarrow> pleq (aug (bsup a b')) (aug a')"
)
  apply(thin_tac
" \<forall>a'. pleq (aug a) (aug a') \<and> (\<forall>bd. pleq bd (aug b) \<longrightarrow> (\<forall>sd. pleq (aug a) sd \<and> pleq bd sd \<and> (\<forall>a'. pleq (aug a) a' \<and> pleq bd a' \<longrightarrow> pleq sd a') \<longrightarrow> pleq sd (aug a'))) \<longrightarrow> pleq (aug (bsup a b)) (aug a')"
)
      apply(rotate_tac -1)
  apply(drule_tac x = bd in spec) apply(auto)

      apply(drule_tac a = bd and b = "aug b" and c = "aug b'" in leq_trans)
       apply(simp) apply(simp)

(* idempotence 1 *)

(* another option instead of the proof below is to use
"bsup a a = a" and associativity. *)

     apply(cut_tac a = a and b = "bsup a b" in bsup_spec)
      apply(simp add:is_least_def l_pleq_def is_bsup_def is_bub_def is_sup_def Pord.is_least_def is_ub_def)
    apply(auto)

(* RHS \<subseteq> LHS *)

     apply(rotate_tac -2)
     apply(drule_tac x = "bsup a b" in spec) apply(auto)

       apply(cut_tac a = a and b = "b" in bsup_spec)
      apply(simp add:is_least_def l_pleq_def is_bsup_def is_bub_def is_sup_def Pord.is_least_def is_ub_def)

     apply(rotate_tac -1)
  apply(drule_tac x = "aug (bsup a b)" in spec) apply(auto)

       apply(cut_tac a = a and b = "b" in bsup_spec)
     apply(simp add:is_least_def l_pleq_def is_bsup_def is_bub_def is_sup_def Pord.is_least_def is_ub_def)

(* LHS \<subseteq> RHS *)

       apply(cut_tac a = a and b = "b" in bsup_spec)
     apply(simp add:is_least_def l_pleq_def is_bsup_def is_bub_def is_sup_def Pord.is_least_def is_ub_def)
    apply(clarsimp)

    apply(rotate_tac -1)
    apply(drule_tac x = "bsup a (bsup a b)" in spec)

    apply(auto)

  apply(drule_tac x = "aug a" in spec) apply(auto)
       apply(cut_tac a = a and b = "b" in bsup_spec)
     apply(simp add:is_least_def l_pleq_def is_bsup_def is_bub_def is_sup_def Pord.is_least_def is_ub_def)

(* idempotence 2 *)

(* bsup_idem *)

(* bsup_assoc *)

(* bsup_sup *)

    apply(case_tac "deaug a")  
     apply(simp add:aug_leq_refl_none)
    apply(drule_tac deaug_aug) apply(clarsimp) apply(rule_tac leq_aug_leq) apply(simp add:leq_refl)

   apply(case_tac "deaug a")
apply(case_tac "deaug b")
     apply(drule_tac aug_leq_leq2) apply(auto)
     apply(case_tac "deaug c")
     apply(drule_tac aug_leq_leq2) apply(auto)


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