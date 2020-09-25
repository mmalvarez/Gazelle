theory LatticeLike_Splitting_Ex imports Main

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
  fixes S :: "('a \<Rightarrow> 'a \<Rightarrow> bool) set"

assumes Ssplit0 : "\<exists> ord . ord \<in> S"

assumes Ssplit1 : "\<And> ord . ord \<in> S \<Longrightarrow> (ord_leq lleq ord) \<and> LatticeLike_Weak_Spec ord"

assumes Ssplit2 :
  "\<And> P . (\<forall> ord . ord \<in> S \<longrightarrow> P ord) \<Longrightarrow> P lleq"

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
definition is_bub' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bub' a b s =
  (lleq a s \<and>
    ((\<forall> lleq' . ord_leq lleq lleq' \<longrightarrow>
                LatticeLike_Weak_Spec lleq' \<longrightarrow>
                lleq' a b \<longrightarrow>
                (lleq' s b))))"

(* lleq' b s or lleq' s b ?
   is_sup or is_ub? *)

definition is_bub :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bub a b s =
  (lleq a s \<and>
    ((\<forall> lleq' . ord_leq lleq lleq' \<longrightarrow>
                LatticeLike_Weak_Spec lleq' \<longrightarrow>
                lleq' a b \<longrightarrow>
                (lleq' b s ))))"

definition is_bub3 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bub3 a b s =
  (lleq a s \<and>
    ((\<forall> lleq' . ord_leq lleq lleq' \<longrightarrow>
                LatticeLike_Weak_Spec lleq' \<longrightarrow>
                lleq' a b \<longrightarrow>
                (lleq' s b \<and> lleq' b s ))))"

definition is_bub4 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bub4 a b s =
  (lleq a s \<and>
    ((\<forall> lleq' . ord_leq lleq lleq' \<longrightarrow>
                LatticeLike_Weak_Spec lleq' \<longrightarrow>
                lleq' s b \<longleftrightarrow>
                lleq' b s)))"
(*
definition is_splitting :: "('a \<Rightarrow> 'a \<Rightarrow> bool) set \<Rightarrow> bool" where
"is_splitting S =
  ((\<forall> ord . ord \<in> S \<longrightarrow> (ord_leq lleq ord \<and>
               LatticeLike_Weak_Spec ord)) \<and>
  (\<forall> a b . (\<forall> ord \<in> S . ord a b) \<longrightarrow> lleq a b))"
  *)             
(*
definition is_bub_new :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bub_new a b s =
  (lleq a s \<and>
    ((\<forall> S ord . is_splitting S \<longrightarrow>
            ord \<in> S \<longrightarrow>
            ord a b \<longrightarrow>
            ord b s)))"
*)

(* is_sup vs is_ub? *)
(* exists, not forall! *)
(*
definition is_bub_sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bub_sup a b s =
  (lleq a s \<and>
      (\<exists> ord . ord \<in> S \<and> ord b s \<and> ord s b) \<and>
      (\<forall> ord .
            ord \<in> S \<longrightarrow>
            ord a b \<longrightarrow>
            (ord b a \<or> ord s b)))"
*)



definition is_bub_weak :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bub_weak a b s =
  (lleq a s \<and>
    ((\<forall> lleq' . ord_leq lleq lleq' \<longrightarrow>
                lleq' a b \<longrightarrow>
                (lleq' b s))))"


(* should this be is_greatest? *)

definition is_bsup' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bsup' a b x = is_greatest (is_bub' a b) x"

definition is_bsup'' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bsup'' a b x = is_least (is_bub' a b) x"

definition is_bsup3 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bsup3 a b x = is_least (is_bub3 a b) x"


definition is_bsup3' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bsup3' a b x = is_greatest (is_bub3 a b) x"


definition is_bsup4 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bsup4 a b x = is_least (is_bub4 a b) x"


definition is_bsup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bsup a b x = is_least (is_bub a b) x"

(*
definition is_bsup_new :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bsup_new a b x = is_least (is_bub_new a b) x"
*)

(*
definition is_bsup_sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bsup_sup a b x = is_least (is_bub_sup a b) x"
*)


(*
definition is_bsup_sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bsup_sup a b s =
  (lleq a s \<and>
  (S =
    {ordn . \<not> (ordn a b) \<and> \<not> (ordn b a) \<and>
            \<not> (ordn b s) \<and> \<not> (ordn s b)} \<union>
    {orde . orde a b \<and> orde b a \<and>
            orde b s \<and> orde s b } \<union>
    {ordl . ordl a b \<and> \<not> (ordl b a) \<and>
            ordl b s \<and> ordl s b}))"
*)

definition is_bsup_sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bsup_sup a b s =
  (lleq a s \<and>
  (\<forall> ord . ord \<in> S \<longrightarrow> 
           (if ord a b then (ord b s \<and> ord s b)
               else (\<not> (ord b s) \<and> \<not> (ord s b)))))"

definition is_bsup_sup_sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bsup_sup_sup a b s =
  is_least (is_bsup_sup a b) s"

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


(*
  assumes bsup_is_bsup_new:
    "\<And> a b . is_bsup_new a b (bsup a b)"
*)
  assumes bsup_is_bsup_sup:
    "\<And> a b . is_bsup_sup_sup a b (bsup a b)"
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

(* closure operator? *)


lemma bsup_sup_sup :
  "\<And> a b . has_sup {a, b} \<Longrightarrow> is_sup {a, b} (bsup a b)"
    apply(cut_tac a = a and b = b in bsup_is_bsup_sup)
  apply(simp add: is_bsup'_def is_bub'_def has_sup_def is_sup_def is_bsup_def is_bub_def is_ub_def is_least_def
        LatticeLike.is_sup_def LatticeLike.is_least_def is_greatest_def is_bsup4_def is_bub4_def
        is_bsup_sup_def is_bsup_sup_sup_def)

  
  apply(auto)

   apply(drule_tac x = s in spec) apply(auto)

       apply(drule_tac x = ord in spec) apply(auto)

  defer

    apply(rotate_tac -1) apply(drule_tac x = s in spec) apply(auto)
    defer
     apply(rotate_tac -6)
     apply(drule_tac Ssplit2)
  apply(auto)
     apply(drule_tac x = ord in spec) apply(clarsimp)
     apply(rotate_tac -1)
  apply(drule_ta

  apply(case_tac "S = {}") apply(auto)
     apply(cut_tac  Ssplit0) apply(clarsimp)

  apply(drule_tac x = x in spec) apply(auto)

  apply(rotate_tac -1)
    apply(drule_tac x = s in spec) apply(auto)
      apply(simp add:LatticeLike.is_ub_def)  defer

  apply(drule_tac x = a' in spec) apply(auto)


     apply(simp add:is_ub_def)
    apply(rotate_tac -3) apply(drule_tac x = a' in spec)
    apply(simp add:is_ub_def)
   apply(drule_tac a = b and b = s and c = "bsup a b" in leq_trans) apply(auto)

  apply(drule_tac x = a' in spec) apply(auto)

  apply(rotate_tac -1) apply(drule_tac x = a' in spec)
  apply(auto) apply(simp add:LatticeLike.is_ub_def)
  apply(auto)

   apply(simp add:is_splitting_def)
   apply(clarsimp)
   apply(drule_tac x = ord in spec; clarsimp)
   apply(drule_tac a = a and b = a' in ord_leq') apply(auto)

   apply(simp add:is_splitting_def)
   apply(clarsimp)
   apply(drule_tac x = ord in spec; clarsimp)
apply(drule_tac a = b and b = a' in ord_leq') apply(auto)
  done

(*
lemma bsup_sup_new :
  "\<And> a b . has_sup {a, b} \<Longrightarrow> is_sup {a, b} (bsup a b)"
    apply(cut_tac a = a and b = b in bsup_is_bsup_new)
  apply(simp add: is_bsup'_def is_bub'_def has_sup_def is_sup_def is_bsup_def is_bub_def is_ub_def is_least_def
        LatticeLike.is_sup_def LatticeLike.is_least_def is_greatest_def is_bsup4_def is_bub4_def
        is_bub_new_def is_bsup_new_def) apply(auto)

   apply(drule_tac x = s in spec) apply(safe)
    apply(drule_tac x = S in spec) apply(simp)
    apply(simp add:is_splitting_def) apply(clarsimp)
    apply(rotate_tac -2) apply(drule_tac x = ord in spec)
    apply(clarsimp)
  apply(drule_tac a = b and b = s in ord_leq') apply(simp) apply(simp)
  apply(drule_tac x =
  "{(\<lambda> a' b' . lleq a' b' \<or> (lleq a' a)),
    lleq}" in spec) apply(clarsimp)
   apply(safe)
    apply(simp add:is_splitting_def)
    apply(safe)
       defer defer
       apply(simp add:ord_leq_def) apply(simp add:LatticeLike_Weak_Spec_def)
  apply(safe)
        apply(simp add:leq_refl)
      apply(drule_tac a = aa and b = ba in leq_trans) apply(simp) apply(simp)
     apply(drule_tac x = "(\<lambda>a' b'. lleq a' b' \<or> lleq a' a)" in spec)
     apply(safe)
        apply(simp add:leq_refl)
           apply(rule_tac b = a in leq_trans; simp)
          apply(simp add:leq_refl)
         apply(rule_tac b = a in leq_trans; simp)
        apply(simp add:leq_refl)
       apply(rule_tac b = a in leq_trans; simp)
      apply(simp add:leq_refl)
     apply(rule_tac b = a in leq_trans; simp)
    apply(drule_tac x = a' in spec) apply(safe)
    apply(simp add:is_splitting_def)
    apply(safe)
  apply(drule_tac x = ord in spec) apply(safe)
    apply(drule_tac a = b and b = a' in ord_leq') apply(simp) apply(simp)

   apply(simp add:ord_leq_def)
  apply(simp add:LatticeLike_Weak_Spec_def)
  apply(safe)
    apply(simp add:leq_refl)
   apply(drule_tac a= aa and b = ba and c = c in leq_trans)  apply(simp) apply(simp)
  apply(drule_tac a= aa and b = ba and c = a in leq_trans)  apply(simp) apply(simp)
  done
*)

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


interpretation Test0 : Mergeable_Spec test0_lleq test0_bsup
  apply(unfold_locales)
     apply(case_tac a; clarsimp) 
    apply(case_tac a; clarsimp)
   apply(case_tac a; clarsimp)
   apply(case_tac b; clarsimp)

  apply(simp add:Mergeable'.is_bsup_weak_def Mergeable'.is_bsup_def Mergeable'.is_bub_def LatticeLike.is_least_def LatticeLike.is_sup_def LatticeLike.is_ub_def
                 Mergeable'.is_bub_weak_def Mergeable'.is_bsup_new_def Mergeable'.is_bub_new_def  
                 Mergeable'.is_bsup_sup_def Mergeable'.is_bub_sup_def)

  apply(auto)
  
    apply(case_tac a; clarsimp)

   apply(simp add:Mergeable'.is_splitting_def)
   apply(auto)
   apply(case_tac a; clarsimp)
    defer
 
    apply(case_tac b; clarsimp)
     defer

     apply(frule_tac x = "Some aa" in spec) apply(auto)

     apply(case_tac "test0_lleq (Some a) (Some aa)")
      apply(auto)

  apply(drule_tac x = "Some aa" in spec; auto)

      defer
      apply(case_tac s'; auto)


  defer

  apply(clarify)
(* 
   apply(simp add: LatticeLike_Weak_Spec_def) 
  apply(case_tac "lleq' (Some a) None") 
    apply(case_tac a; clarsimp)
   apply(case_tac a; clarsimp)

  apply(drule_tac x = test0_lleq in spec) apply(simp) apply(auto)
     apply(simp add:ord_leq_refl)
(* shouldn't need to reprove this. *)
    apply(simp add: LatticeLike_Weak_Spec_def) apply(auto)
    apply(case_tac ab; clarsimp)
   apply(case_tac ab; clarsimp)

  apply(case_tac b; auto)
   defer

   apply(simp add:LatticeLike_Weak_Spec_def)
  apply(auto)
    
    apply(simp cong:option.case_cong)
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