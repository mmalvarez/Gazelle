theory Prod_Merge_Concrete imports Prod_Merge "../Reify"
begin


(* we need to axiomatize a type c
   isomorphic to the set of f : a \<Rightarrow> b such that
   forall (a : a), cross (f a) = a
*)


typedef ('a, 'b) cross =
   "{((f :: 'a \<Rightarrow> 'b \<Rightarrow> 'b), (g :: 'b \<Rightarrow> 'a \<Rightarrow> 'a)) .
     (\<forall> a' b' a'' b'' . (f a' b' = b'' \<longrightarrow> g b'' a' = a')
              \<and> (g b' a' = a'' \<longrightarrow> f a'' b' = b')
              \<and> (f a' (f a'' b') = f a' b')
              \<and> (g b' (g b'' a') = g b' a')
              \<and> (f (g b' a') b' = b')
              \<and> (g (f a' b') a' = a'))}"
  apply(rule_tac x = "((\<lambda> a b . b), (\<lambda> b a . a))" in exI)
  apply(simp)
  done

type_synonym ('a, 'b) cross' = "('a \<Rightarrow> 'b \<Rightarrow> 'b) * ('b \<Rightarrow> 'a \<Rightarrow> 'a)"

definition cross_spec :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) * ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool"
  where
"cross_spec fg =
   (case fg of (f, g) \<Rightarrow>
     (\<forall> a' b' a'' b'' . (f a' b' = b'' \<longrightarrow> g b'' a' = a')
              \<and> (g b' a' = a'' \<longrightarrow> f a'' b' = b')
              \<and> (f a' (f a'' b') = f a' b')
              \<and> (g b' (g b'' a') = g b' a')
              \<and> (f (g b' a') b' = b')
              \<and> (g (f a' b') a' = a')))"

(*
typedef ('a, 'b) pmc_target2 =
  "{ (f :: ('a, 'b) cross' \<Rightarrow> ('a * 'b)) .
     \<forall> c . ((fst c) (fst (f c)) (snd (f c)) = snd (f c))}"
  apply(rule_tac x = "(\<lambda> c . 
    (SOME (a, b) . b = (fst c a b)))" in exI)
  apply(simp)
  apply(rule_tac allI)
  apply(auto)
  apply(auto simp add:cross_spec_def)
  apply(case_tac "(SOME (aa, b). b = a aa b)") apply(clarsimp)

  apply(cut_tac x = "(aa, b)" and P = "(\<lambda> (aa, b) . b = a aa b)" in SMT.verit_sko_ex_indirect)
   apply(auto)
  apply(rotate_tac -1)
  apply(drule_tac x = "b ba aa" in spec) apply(rotate_tac -1)
  apply(drule_tac x = ba in spec) 
 
  done
*)

(* this doesn't work either - does not constrain 
   c enough *)
(*
typedef ('a, 'b) pmc_target =
  "{ (x :: 'a, y :: 'b) .
     (\<exists> c c1 c2 . c = (c1, c2) \<and> cross_spec c   \<and>
      ((c1) (x) (y) = y))}"
  
  apply(rule_tac x = "(undefined, undefined)" in exI)
  apply(auto)
  apply(rule_tac x = "(\<lambda> a b . b)" in exI) apply(auto)
  apply(rule_tac x = "(\<lambda> b a . a)" in exI)
  apply(auto simp add:cross_spec_def)
  done
*)

typedef ('a, 'b) pmc_target =
  "{ (f :: ('a, 'b) cross \<Rightarrow> ('a * 'b)) .
     (\<forall> c c1 c2 . Rep_cross c = (c1, c2)  \<longrightarrow> 
      ((c1) (fst (f c)) (snd (f c)) = snd (f c)))}"
  apply(rule_tac x = "(\<lambda> c . 
    (case (Rep_cross c) of (c1, c2) \<Rightarrow>
    (SOME (a, b) . b = (c1 a b))))" in exI)
  apply(simp)
  apply(rule_tac allI)
  apply(auto split:prod.splits)
  apply(case_tac "(SOME (a, b). b = x1 a b)") apply(clarsimp)

  apply(cut_tac x = "(a, b)" and P = "(\<lambda> (a, b) . b = x1 a b)" in SMT.verit_sko_ex_indirect)
   apply(auto)
  apply(cut_tac x = "c" in Rep_cross)
  apply(auto)
  apply(drule_tac x = "x2 b a" in spec)
  apply(rotate_tac -1) apply(drule_tac x = b in spec)
  apply(clarsimp)
  done


(*
typedef ('a, 'b) pmc_target =
  "{ (f :: ('a, 'b) cross' \<Rightarrow> ('a * 'b)) .
     \<forall> c . cross_spec c \<longrightarrow> ((fst c) (fst (f c)) (snd (f c)) = snd (f c))}"
  apply(rule_tac x = "(\<lambda> c . 
    (SOME (a, b) . b = (fst (Rep_cross c) a b)))" in exI)
  apply(simp)
  apply(rule_tac allI)
  apply(cut_tac x = c in Rep_cross)
  apply(clarsimp)
  apply(case_tac "(SOME (a, b). b = x a b)") apply(clarsimp)
  apply(cut_tac x = "(a, b)" and P = "(\<lambda> (a, b) . b = x a b)" in SMT.verit_sko_ex_indirect)
   apply(clarsimp)
  apply(auto)
  apply(rotate_tac -1)
  apply(drule_tac x = "(y b a)" in spec) apply(rotate_tac -1)
  apply(drule_tac x = b in spec) apply(auto)
  done
*)
(*
locale PMC' =
  fixes r1 :: "'a \<Rightarrow> reified"
  fixes d1 :: "reified \<Rightarrow> 'a option"
  fixes r2 :: "'b \<Rightarrow> reified"
  fixes d2 :: "reified \<Rightarrow> 'b option"

locale PMC = PMC' +
  RA : reiden r1 d1 +
  RB : reiden r2 d2 +
  fixes cross1 :: "'b \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes cross2 :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
 
begin

print_context
*)

fun proj1' :: "('a, 'b) cross \<Rightarrow> ('a, 'b) pmc_target \<Rightarrow> 'a" where
"proj1' c p = 
  (fst (Rep_pmc_target p c))"

fun proj2' :: "('a, 'b) cross \<Rightarrow> ('a, 'b) pmc_target \<Rightarrow> 'b" where
"proj2' c p = 
  (snd (Rep_pmc_target p c))"

(*
fun upd1 :: "'a * ('a, 'b) pmc_target \<Rightarrow> ('a, 'b) pmc_target" where
  "upd1 (a, p) =
  (Abs_pmc_target (\<lambda> c . 
    (case (Rep_pmc_target p c, Rep_cross c) of
      ((a', b'), f, g) \<Rightarrow> (a, f a b'))))"
*)

(*
fun upd1 :: "('a, 'b) cross \<Rightarrow> 'a * ('a, 'b) pmc_target \<Rightarrow> ('a * 'b)" where
  "upd1 c (a, p) =
  (Abs_pmc_target (\<lambda> c . 
    (case (Rep_pmc_target p c, Rep_cross c) of
      ((a', b'), f, g) \<Rightarrow> (a, f a b'))))"
*)
fun upd1 :: "('a, 'b) cross \<Rightarrow> 'a * ('a, 'b) pmc_target \<Rightarrow> ('a * 'b)" where
  "upd1 c (a, p) =
  (case (Rep_pmc_target p c, Rep_cross c) of
      ((a', b'), f, g) \<Rightarrow> (a, f a b'))"

(*
fun upd1 :: "('a, 'b) cross \<Rightarrow> 'a * ('a, 'b) pmc_target \<Rightarrow> ('a, 'b) pmc_target" where
  "upd1 cx (a, p) =
  (Abs_pmc_target (\<lambda> c . 
    (case (Rep_pmc_target p cx, Rep_cross cx) of
      ((a', b'), f, g) \<Rightarrow> (a, f a b'))))"
fun upd2 :: "'b * ('a, 'b) pmc_target \<Rightarrow> ('a, 'b) pmc_target" where
  "upd2 (b, p) =
  (Abs_pmc_target (\<lambda> c . 
    (case (Rep_pmc_target p c, Rep_cross c) of
      ((a', b'), f, g) \<Rightarrow> (g b a', b))))"
*)
lemma funex' :
  fixes f g :: "'a \<Rightarrow> 'b"
  shows "f \<noteq> g \<Longrightarrow> (\<exists> a . f a \<noteq> g a)"
  apply(auto)
  done

lemma funex :
  fixes f g :: "'a \<Rightarrow> 'b"
  shows "(\<And> a . f a = g a) \<Longrightarrow> f = g"
  apply(blast)
  done


(* upd1 also needs to take a cr? *)
lemma PutGet : "\<And> c . Abs_pmc_target (\<lambda> cr . upd1 cr (proj1' cr c, c)) = c"
  apply(simp)
apply(induct_tac c rule: Abs_pmc_target_induct)
  apply(auto)

  apply(cut_tac x ="(\<lambda>cr. case Rep_pmc_target (Abs_pmc_target y) cr of
                 (a', b') \<Rightarrow>
                   case Rep_cross cr of
                   (f, g) \<Rightarrow>
                     (fst (Rep_pmc_target (Abs_pmc_target y) cr),
                      f (fst (Rep_pmc_target (Abs_pmc_target y) cr)) b'))"
and y = y in Abs_pmc_target_inject)

    apply(auto  split:prod.splits)
   apply(cut_tac x = c in Rep_cross) apply(clarsimp)
  apply(drule_tac funex')

  apply(clarsimp)
    apply(auto  split:prod.splits)

  apply(cut_tac y = y in Abs_pmc_target_inverse)
   apply(auto)
  apply(drule_tac x = a in spec) apply(auto)
  done

locale whoa =
  fixes crs :: "('a, 'b) cross"

begin

lemma PutGet2 : "\<And> c .  upd1 crs (proj1' crs c, c) = Rep_pmc_target c crs"
  apply(cut_tac c=c in PutGet)
  apply(auto split:prod.splits)
  apply(cut_tac x = c in Rep_pmc_target) apply(auto)
(*
abbreviation proj1 :: "('a, 'b) pmc_target \<Rightarrow> 'a" where
"proj1 t \<equiv> proj1' crs t"

abbreviation proj2 :: "('a, 'b) pmc_target \<Rightarrow> 'b" where
"proj2 t \<equiv> proj2' crs t"
*)
(*
fun proj1 :: "('a, 'b) pmc_target \<Rightarrow> 'a" where
"proj1 p =
  (case Rep_pmc_target p of (a, b) \<Rightarrow> a)"

fun upd1 :: "'a * ('a, 'b) pmc_target \<Rightarrow> ('a, 'b) pmc_target" where
"upd1 (a, p) =
  (case Rep_pmc_target p of (a', b') \<Rightarrow> Abs_pmc_target (a, (fst crs) a b'))"

fun upd2 :: "'b * ('a, 'b) pmc_target \<Rightarrow> ('a, 'b) pmc_target" where
"upd2 (b, p) =
  (case Rep_pmc_target p of (a', b') \<Rightarrow> Abs_pmc_target ((snd crs) b a', b))"
*)

(*
fun proj2 :: "('a, 'b) pmc_target \<Rightarrow> 'b" where
"proj2 p =
  (case Rep_pmc_target p of (a, b) \<Rightarrow> b)"
*)
(* remember - we can't prove putget for the weird one with function *)
lemma GetPut : "\<And> m1c . proj1 (upd1 m1c) = fst m1c"
  apply(auto)
   apply(auto split:prod.splits)
  apply(case_tac crs) apply(auto)
  apply(cut_tac y = " (a, aa a x2)"
in Abs_pmc_target_inverse)
   apply(auto split:prod.splits)
  apply(rule_tac x = aa in exI) apply(auto)
   apply(rule_tac x = ba in exI) 
  apply(cut_tac Hcrs)
   apply(auto simp add: Hcrs)
apply(cut_tac Hcrs) apply(simp add:cross_spec_def)
  done

lemma PutGet : "\<And> c . upd1 (proj1 c, c) = c"
  apply(auto)
  apply(auto split:prod.splits)

  apply(case_tac c) apply(auto)
(*
  apply(cut_tac x = "  (x1, fst crs x1 x2)" and y = "(a, b)" in Abs_pmc_target_inject)
    apply(simp add: Hcrs cross_spec_def)
*)
  apply(cut_tac y = "(a, b)" in
    Abs_pmc_target_inverse) apply(auto)

apply(cut_tac x = "Abs_pmc_target (x1, x2)" in
    Rep_pmc_target) apply(auto)
  apply(case_tac crs) apply(auto)

  apply(cut_tac x = "Abs_pmc_target (x1, fst crs x1 x2)"
in Rep_pmc_target) apply(auto)


apply(cut_tac y = "(x1, fst crs x1 x2)"
 in
    Abs_pmc_target_inverse) apply(auto)

   apply(rule_tac x = "fst crs" in exI)
   apply(case_tac crs, auto)
    apply(rule_tac x = bc in exI) apply(cut_tac Hcrs) apply(auto)
  apply(cut_tac Hcrs) apply(simp add:cross_spec_def)


     apply(rule_tac x = aa in exI)
     apply(auto)
     apply(rule_tac x = ba in exI) apply(simp add:cross_spec_def)



  apply(cut_tac x = " (\<lambda>c. case Rep_pmc_target (Abs_pmc_target y) c of
              (a', b') \<Rightarrow>
                case Rep_cross c of
                (f, g) \<Rightarrow> (fst (Rep_pmc_target (Abs_pmc_target y) cr), f (fst (Rep_pmc_target (Abs_pmc_target y) cr)) b'))"
and y = y in Abs_pmc_target_inject)
   apply(case_tac cr, auto)
   apply(drule_tac x = c in  spec)
   apply(auto)
   apply(case_tac c) apply(auto)

   apply(cut_tac y = "(aa, ba)" in Abs_cross_inverse)
    apply(auto)

  apply(drule_tac funex') apply(auto)
  apply(auto split: prod.splits)
  apply(case_tac "(Rep_pmc_target (Abs_pmc_target y) cr)", auto)
  apply(case_tac cr, auto)
  apply(case_tac a, auto)
  apply(drule_tac x = "Abs_cross (ac, bb)" in spec)
  apply(auto)
  apply(case_tac "y (Abs_cross (ac, bb))", auto)
  apply(drule_tac x = a in spec)
  apply(auto)
  apply(case_tac "y a", auto)

  apply(case_tac "Abs_pmc_target
        (\<lambda>c. case Rep_pmc_target (Abs_pmc_target y) c of
              (a', b') \<Rightarrow>
                case Rep_cross c of
                (f, g) \<Rightarrow> (fst (Rep_pmc_target (Abs_pmc_target y) cr), f (fst (Rep_pmc_target (Abs_pmc_target y) cr)) b'))")
  

   apply(case_tac c) apply(auto)
  apply(cut_tac 

  case (Abs_pmc_target y)
  then show ?case 
qed
  apply(auto)
  apply(cut_tac x = c in Rep_pmc_target) apply(auto)
  apply(case_tac " Abs_pmc_target
          (\<lambda>ca. case Rep_pmc_target c ca of
                 (a', b') \<Rightarrow>
                   case Rep_cross ca of (f, g) \<Rightarrow> (fst (Rep_pmc_target c crs), f (fst (Rep_pmc_target c crs)) b'))")
  apply(auto)
  apply(case_tac c, auto)
  apply(case_tac
" Abs_pmc_target
        (\<lambda>c. case Rep_pmc_target (Abs_pmc_target y) c of
              (a', b') \<Rightarrow>
                case Rep_cross c of
                (f, g) \<Rightarrow>
                  (fst (Rep_pmc_target (Abs_pmc_target y) (Abs_cross (a, b))),
                   f (fst (Rep_pmc_target (Abs_pmc_target y) (Abs_cross (a, b)))) b'))")
  apply(auto)
  apply(cut_tac x = y and y = ya in Abs_pmc_target_inject)
    apply(auto)
  apply(drule_tac funex') apply(auto)
  apply(case_tac aa, auto) apply(rotate_tac 2)
  apply(drule_tac x = "Abs_cross (ab, ba)" in spec)
  apply(cut_tac x = "Abs_cross (ab, ba)" in Rep_cross) apply(auto)
  apply(auto)
  apply(cut_tac x =
" (Abs_pmc_target y)"
in Rep_pmc_target) apply(auto)
  apply(case_tac "Abs_pmc_target y")
  apply(auto split:prod.splits)

  apply(cut_tac x = "(\<lambda>c. case Rep_pmc_target (Abs_pmc_target y) c of
              (a', b') \<Rightarrow>
                case Rep_cross c of
                (f, g) \<Rightarrow>
                  (fst (Rep_pmc_target (Abs_pmc_target y) (Abs_cross (a, b))),
                   f (fst (Rep_pmc_target (Abs_pmc_target y) (Abs_cross (a, b)))) b'))" and
y = y in Abs_pmc_target_inject)
    apply(auto)
   apply(auto split: prod.splits)
   apply(case_tac "(Rep_pmc_target (Abs_pmc_target y) (Abs_cross (a, b)))", auto)
  apply(cut_tac x = c in Rep_cross) apply(auto)
  apply(cut_tac x = "(Abs_pmc_target y)"
in Rep_pmc_target) apply(auto)
  apply(drule_tac funex', auto)
   apply(auto split: prod.splits)
   apply(case_tac "(Rep_pmc_target (Abs_pmc_target y) (Abs_cross (a, b)))", auto)
  apply(cut_tac x = aa in Rep_cross) apply(auto)
  apply(cut_tac x = "(Abs_pmc_target y)"
in Rep_pmc_target) apply(auto)
  apply(rotate_tac 4)
  apply(drule_tac x = "(Abs_cross (a, b))" in spec)
  apply(rotate_tac -1) apply(drule_tac x = a in spec)
  apply(auto)
  apply(cut_tac x = "Abs_cross (a, b)"
in Rep_cross) apply(auto)
  apply(cut_tac y = "(a, b)"
in Abs_cross_inverse) apply(auto)


  apply(case_tac "y( Abs_cross (a, b))") apply(auto)

lemma Coh :
  fixes c c'
  shows "upd1 (proj1 c, upd2 (proj2 c, c')) =
         upd2 (proj2 c, upd1 (proj1 c, c'))"

  apply(clarsimp) 
  apply(cut_tac
x = "(\<lambda>ca. case Rep_pmc_target
                  (Abs_pmc_target
                    (\<lambda>ca. case Rep_pmc_target c' ca of
                           (a', b') \<Rightarrow>
                             case Rep_cross ca of
                             (f, g) \<Rightarrow> (g (snd (Rep_pmc_target c crs)) a', snd (Rep_pmc_target c crs))))
                  ca of
            (a', b') \<Rightarrow> case Rep_cross ca of (f, g) \<Rightarrow> (fst (Rep_pmc_target c crs), f (fst (Rep_pmc_target c crs)) b'))"
and y = "(\<lambda>ca. case Rep_pmc_target
                  (Abs_pmc_target
                    (\<lambda>ca. case Rep_pmc_target c' ca of
                           (a', b') \<Rightarrow>
                             case Rep_cross ca of
                             (f, g) \<Rightarrow> (fst (Rep_pmc_target c crs), f (fst (Rep_pmc_target c crs)) b')))
                  ca of
            (a', b') \<Rightarrow> case Rep_cross ca of (f, g) \<Rightarrow> (g (snd (Rep_pmc_target c crs)) a', snd (Rep_pmc_target c crs)))"
in Abs_pmc_target_inject)
    apply(clarsimp)
    apply(auto split: prod.splits)   

    apply(cut_tac x = c in Rep_pmc_target) apply(auto)
  apply(rotate_tac -1)
    apply(drule_tac x = crs in spec)
    apply(case_tac "Rep_cross crs") apply(auto)
    apply(case_tac "(Rep_pmc_target c crs)") apply(auto)
    apply(cut_tac x = ca in Rep_cross) apply(auto)


    apply(cut_tac x = c in Rep_pmc_target) apply(auto)
  apply(rotate_tac -1)
    apply(drule_tac x = crs in spec)
    apply(case_tac "Rep_cross crs") apply(auto)
    apply(case_tac "(Rep_pmc_target c crs)") apply(auto)
   apply(cut_tac x = ca in Rep_cross) apply(auto)

(* begin experiment *)

  apply(thin_tac "Abs_pmc_target
          (\<lambda>ca. case Rep_pmc_target
                       (Abs_pmc_target
                         (\<lambda>ca. case Rep_pmc_target c' ca of
                                (a', b') \<Rightarrow> case Rep_cross ca of (f, g) \<Rightarrow> (g (snd (Rep_pmc_target c crs)) a', snd (Rep_pmc_target c crs))))
                       ca of
                 (a', b') \<Rightarrow> case Rep_cross ca of (f, g) \<Rightarrow> (fst (Rep_pmc_target c crs), f (fst (Rep_pmc_target c crs)) b')) \<noteq>
         Abs_pmc_target
          (\<lambda>ca. case Rep_pmc_target
                       (Abs_pmc_target
                         (\<lambda>ca. case Rep_pmc_target c' ca of
                                (a', b') \<Rightarrow> case Rep_cross ca of (f, g) \<Rightarrow> (fst (Rep_pmc_target c crs), f (fst (Rep_pmc_target c crs)) b')))
                       ca of
                 (a', b') \<Rightarrow> case Rep_cross ca of (f, g) \<Rightarrow> (g (snd (Rep_pmc_target c crs)) a', snd (Rep_pmc_target c crs)))")

  apply(drule_tac funex') apply(auto)

(*end experiment *)

(*
  apply(auto split: prod.splits)
  apply(cut_tac x =
"(Abs_pmc_target
          (\<lambda>ca. case Rep_pmc_target c' ca of
                 (a', b') \<Rightarrow>
                   case Rep_cross ca of
                   (f, g) \<Rightarrow> (fst (Rep_pmc_target c crs), f (fst (Rep_pmc_target c crs)) b')))"
in Rep_pmc_target) apply(auto)
  apply(case_tac crs) apply(auto)
*)
  apply(auto split: prod.splits)
  apply(case_tac "(Rep_pmc_target c crs)", auto)

  apply(cut_tac x =
"(Abs_pmc_target (\<lambda>ca. case Rep_pmc_target c' ca of (a', b') \<Rightarrow> case Rep_cross ca of (f, g) \<Rightarrow> (aa, f aa b')))" in Rep_pmc_target) apply(auto)
   apply(drule_tac x = a in spec) apply(auto)

  apply(cut_tac x =
"(Abs_pmc_target (\<lambda>ca. case Rep_pmc_target c' ca of (a', b') \<Rightarrow> case Rep_cross ca of (f, g) \<Rightarrow> (g b a', b)))"
in Rep_pmc_target)  apply(auto)
   apply(drule_tac x = a in spec) apply(auto)

    apply(cut_tac x = c in Rep_pmc_target) apply(auto)
   apply(drule_tac x = crs in spec) apply(auto)
   apply(case_tac crs) apply(auto)
   apply(rename_tac boo)
   apply(drule_tac x = ab in spec)
   apply(auto)
    apply(cut_tac y = "(ab, boo)" in Abs_cross_inverse)
  apply(auto)

    apply(cut_tac x = c in Rep_pmc_target) apply(auto)
  apply(rotate_tac -1)
   apply(drule_tac x = crs in spec) apply(auto)
   apply(rotate_tac -1)
   apply(drule_tac x = ab in spec)
   apply(auto)
    apply(cut_tac y = "(ab, boo)" in Abs_cross_inverse)
  apply(auto)

  apply(case_tac "(Rep_pmc_target c crs)", auto)
    apply(cut_tac x = c in Rep_pmc_target) apply(auto)
  apply(cut_tac x = c' in Rep_pmc_target) apply(auto)

  apply(case_tac a) apply(auto)
   apply(drule_tac x = "Abs_cross (aa, b)" in spec)
   apply(rotate_tac -1) apply(drule_tac x = aa in spec)
   apply(auto)

  apply(cut_tac y = " (aa, b)" in
    Abs_cross_inverse)
     apply(clarsimp)
     apply(auto)

  apply(cut_tac y = " (aa, b)" in
    Abs_cross_inverse)
     apply(clarsimp)
     apply(auto)


   apply(drule_tac x = crs in spec)
  apply(case_tac crs) apply(auto)
   apply(rotate_tac -3)
   apply(drule_tac x = a in spec)
   apply(auto)
    apply(rotate_tac -1)
    apply(drule_tac x = b in spec)
    apply(cut_tac y = "(aa, b)" in Abs_cross_inverse)
     apply(auto)

   apply(case_tac c, auto)
   apply(case_tac "(Rep_pmc_target (Abs_pmc_target y) (Abs_cross (aa, b)))")
  apply(auto)
  apply(auto split: prod.splits)


  apply(case_tac "Rep_pmc_target c crs") apply(auto)
  apply(drule_tac funex') apply(auto)

  apply(auto split: prod.splits)  
  apply(cut_tac y = "(\<lambda>ca. case Rep_pmc_target c' ca of (a', b') \<Rightarrow> case Rep_cross ca of (f, g) \<Rightarrow> (a, f a b'))"
in Abs_pmc_target_inverse) apply(auto)
  apply(auto split: prod.splits)  

    apply(cut_tac x = ca in Rep_cross) apply(auto)

   apply(case_tac c) apply(case_tac c') apply(auto)
   apply(case_tac aa) apply(clarsimp)
   apply(cut_tac y = "(a, ba)" in Abs_cross_inverse)
    apply(auto)

  apply(cut_tac y =
"(\<lambda>ca. case Rep_pmc_target (Abs_pmc_target ya) ca of (a', b') \<Rightarrow> case Rep_cross ca of (f, g) \<Rightarrow> (g b a', b))"
in Abs_pmc_target_inverse)
  apply(auto)
    apply(cut_tac x = ca in Rep_cross) apply(auto split:prod.splits)
   apply(case_tac crs) apply(auto)
   apply(cut_tac y = y in Abs_pmc_target_inverse)
    apply(auto)
   apply(cut_tac y = ya in Abs_pmc_target_inverse)
  apply(auto)
   apply(cut_tac x = "Abs_pmc_target ya" in
Rep_pmc_target)
   apply(auto)
   apply(cut_tac x = "Abs_pmc_target y" in
Rep_pmc_target)
   apply(auto)

   apply(rotate_tac -12)
   apply(drule_tac x = "Abs_cross (a, b)" in spec)
   apply(rotate_tac -1)
   apply(drule_tac x = a in spec) apply(rotate_tac -1)
   apply(auto)
    apply(case_tac crs) apply(auto)
  apply(rotate_tac -3)
    apply(drule_tac x = b in spec)
  apply(cut_tac x = "(aa, ba)" and y = "(a, b)" in Abs_cross_inject)
  apply(auto)

  apply(cut_tac y = "(a, b)" in Abs_cross_inverse) apply(auto)
    apply(cut_tac y = "(x1a, x2a)" in Abs_cross_inverse) apply(auto)

  apply(cut_tac x = " (Abs_pmc_target
          (\<lambda>ca. case Rep_pmc_target (Abs_pmc_target ya) ca of (a', b') \<Rightarrow> case Rep_cross ca of (f, g) \<Rightarrow> (x1, f x1 b')))"
in Rep_pmc_target)
   apply(auto)

   apply(rotate_tac -1)
   apply(drule_tac x = "Abs_cross (x1a, x2a)" in spec)
   apply(rotate_tac -1)
  apply(drule_tac x = x1a in spec)
   apply(simp split:prod.splits)
  apply(cut_tac y = "(a, b)" in Abs_cross_inverse)
    apply(auto)

  apply(cut_tac x =
"Abs_pmc_target (\<lambda>ca. case ya ca of (a', b') \<Rightarrow> case Rep_cross ca of (f, g) \<Rightarrow> (x1, f x1 b'))"
in Rep_pmc_target)
   apply(auto)
  apply(rotate_tac -1)
   apply(drule_tac x = "Abs_cross (x1a, x2a)" in spec)
   apply(rotate_tac -1)
  apply(drule_tac x = x1a in spec) apply(auto)
  apply(case_tac "(x1c, x2c)")
  apply(cut_tac y = "(\<lambda>ca. case Rep_pmc_target (Abs_pmc_target ya) ca of (a', b') \<Rightarrow> case Rep_cross ca of (f, g) \<Rightarrow> (g b a', b))"
in Abs_pmc_target_inverse)
apply(cut_tac y = "y"
in Abs_pmc_target_inverse)
    apply(auto split: prod.splits)  
    apply(cut_tac x = ca in Rep_cross) apply(auto)
    apply(auto split: prod.splits)  

   apply(cut_tac x = c in Rep_pmc_target) apply(auto)
    apply(cut_tac x = c' in Rep_pmc_target) apply(auto)

  apply(cut_tac x = aa in Rep_cross) apply(clarsimp)
   apply(case_tac c') apply(case_tac c)
  apply(case_tac crs)
   apply(auto)
  apply(case_tac "Rep_pmc_target c crs")
   apply(clarsimp)
  apply(case_tac aa)
    apply(auto split: prod.splits)   
  apply(cut_tac y = " (\<lambda>ca. case Rep_pmc_target (Abs_pmc_target y) ca of (a', b') \<Rightarrow> case Rep_cross ca of (f, g) \<Rightarrow> (g bb a', bb))"
in Abs_pmc_target_inverse)
    apply(auto split:prod.splits)
    apply(cut_tac x = ca in Rep_cross) apply(auto)

  apply(cut_tac y = 
"(\<lambda>ca. case Rep_pmc_target (Abs_pmc_target y) ca of (a', b') \<Rightarrow> case Rep_cross ca of (f, g) \<Rightarrow> (ac, f ac b'))" in
Abs_pmc_target_inverse)
    apply(auto split:prod.splits)
    apply(cut_tac x = ca in Rep_cross) apply(auto)
  apply(cut_tac y = ya in Abs_pmc_target_inverse)
  apply(auto)
    apply(cut_tac x = x2a in Rep_cross) apply(auto)

    apply(simp add: cross_spec_def)

    apply(case_tac c') apply(clarsimp)
  apply(case_tac "Rep_pmc_target c crs")
    apply(clarsimp)
   apply(simp add: cross_spec_def)
  apply(simp split: prod.splits)

  apply(clarsimp)
  apply(drule_tac funex')
  apply(auto split:prod.splits)

  apply(case_tac crs) apply(auto)

  apply(cut_tac x = c in Rep_pmc_target) apply(auto)
  apply(cut_tac x = c' in Rep_pmc_target) apply(auto)

  apply(case_tac crs) apply(auto)
  apply(case_tac c) apply(auto split:prod.splits)
apply(case_tac c') apply(auto split:prod.splits)
  apply(case_tac "Rep_pmc_target (Abs_pmc_target y) (aa, ba)") apply(auto)

  apply(cut_tac y =
"(\<lambda>ca. case Rep_pmc_target (Abs_pmc_target ya) ca of (a', b') \<Rightarrow> case ca of (f, g) \<Rightarrow> (g bb a', bb))"
in Abs_pmc_target_inverse)
   apply(auto split:prod.splits)
  defer

   apply(drule_tac x = ab in spec)
   apply(auto)
     apply(cut_tac y = y in Abs_pmc_target_inverse)
  apply(auto)
  apply(cut_tac x = "(Abs_pmc_target y)" in
Rep_pmc_target)
     apply(rotate_tac -1) apply(drule_tac Set.CollectD)
  apply(rotate_tac -1)
  apply(drule_tac x = "(aa, ba)" in spec) 
     apply(simp)
  apply(cut_tac Hc) apply(simp add:cross_spec_def)
  apply(cut_tac x = 
" (Abs_pmc_target (\<lambda>ca. case Rep_pmc_target (Abs_pmc_target ya) ca of (a', b') \<Rightarrow> case ca of (f, g) \<Rightarrow> (g bb a', bb)))"
in Rep_pmc_target) apply(auto)
    apply(cut_tac x = c in Rep_pmc_target) apply(auto)


  apply
  apply(cut_tac x = aa in Rep_cross) apply(clarsimp)

  apply(case_tac c') apply(auto)
  apply(case_tac "(Abs_pmc_target
          (\<lambda>ca. case Rep_pmc_target (Abs_pmc_target ya) ca of (a', b') \<Rightarrow> case Rep_cross ca of (f, g) \<Rightarrow> (g b a', b)))")
  apply(auto)
  apply(case_tac crs) apply(auto)
  apply(cut_tac y = ya in "Abs_pmc_target_inverse")
   apply(auto)
  apply(cut_tac y = "(ab, ba)" in Abs_cross_inverse)
  apply(auto)
  apply(rotate_tac -12) apply(drule_tac spec) apply(rotate_tac -1) apply(auto)
  apply(drule_tac spec)
  apply(auto)
    apply(drule_tac spec) apply(rotate_tac -1)
  apply(drule_tac x = b in spec)
  apply(auto)
  apply(cut_tac y = "((\<lambda>ca. case ya ca of (a', b') \<Rightarrow> case Rep_cross ca of (f, g) \<Rightarrow> (x2a b x1, f (x2a b x1) b')))" in "Abs_pmc_target_inverse")
  apply(auto)
   apply(auto  split: prod.splits)
  apply(cut_tac x = ca in Rep_cross) apply(auto)
  apply(rotate_tac -1) apply(drule_tac a = 
"(Abs_cross (ab, ba))" in funex) apply(auto)
    apply(cut_tac x = c' in Rep_pmc_target)
  apply(auto)
  apply(rotate_tac -4)
  apply(drule_tac x = a in spec)
  apply(auto)

  apply(case_tac crs) apply(auto)
    apply(case_tac aa) apply(clarsimp)

  apply(cut_tac y = "(\<lambda>ca. case Rep_pmc_target (Abs_pmc_target ya) ca of (a', b') \<Rightarrow> case Rep_cross ca of (f, g) \<Rightarrow> (g b a', b))"
  in Abs_pmc_target_inverse)
     apply(auto split: prod.splits)
apply(cut_tac x = "Abs_cross (ac, bb)" in Rep_cross) apply(auto)
     apply(cut_tac x = "ca" in Rep_cross) apply(auto)

apply(cut_tac x = "Abs_cross (ac, bb)" in Rep_cross) apply(auto)
apply(cut_tac x = "ca" in Rep_cross) apply(auto)
     apply(case_tac ca, clarsimp)
apply(split prod.splits)
  apply(case_tac c') apply(clarsimp)
  apply(case_tac c) apply(clarsimp)
  apply(simp add: Abs_pmc_target_inject)

  apply(cut_tac y = "((a, b), aa, ba)" in Abs_pmc_target_inverse) apply(clarsimp)
  apply(clarsimp)
  apply(cut_tac y = "((ab, bb), ac, bc)" in Abs_pmc_target_inverse) apply(clarsimp)
  apply(clarsimp)
  apply(cut_tac y = "((ba bb a, bb), aa, ba)" in Abs_pmc_target_inverse)
   apply(clarsimp)
  apply(clarsimp)
  apply(cut_tac y = " ((ab, aa ab b), aa, ba)" in Abs_pmc_target_inverse)
   apply(clarsimp)
  apply(clarsimp)
  apply(cut_tac x = "Abs_pmc_target ((ab, aa ab bb), aa, ba)"
        and y = "Abs_pmc_target ((ba bb ab, bb), aa, ba)" in Rep_pmc_target_inject)
  apply(clarsimp)

(*
(* new idea: parameterize this by f1, g1, which will be locally fixed *)
typedef ('a, 'b) pmc_target =
  "{ ((a :: 'a, b :: 'b), (f :: 'a \<Rightarrow> 'b \<Rightarrow> 'b), (g :: 'b \<Rightarrow> 'a \<Rightarrow> 'a)) .
     (\<forall> a' b' a'' b'' . (f a' b' = b'' \<longrightarrow> g b'' a' = a')
              \<and> (g b' a' = a'' \<longrightarrow> f a'' b' = b')
              \<and> (f a' (f a'' b') = f a' b')
              \<and> (g b' (g b'' a') = g b' a')
              \<and> (f (g b' a') b' = b')
              \<and> (g (f a' b') a' = a')) \<and>
     f a b = b}"
  apply(rule_tac x = "((undefined, undefined), (\<lambda> a b . b), (\<lambda> b a . a))" in exI)
  apply(simp)
  done
*)

(*
fun proj1 :: "('a, 'b) pmc_target \<Rightarrow> 'a" where
"proj1 p = 
  fst (fst (Rep_pmc_target p))"

fun proj2 :: "('a, 'b) pmc_target \<Rightarrow> 'b" where
"proj2 p = 
  snd (fst (Rep_pmc_target p))"

fun upd1 :: "'a * ('a, 'b) pmc_target \<Rightarrow> ('a, 'b) pmc_target" where
  "upd1 (a, p) =
    (case Rep_pmc_target p of
      ((a', b'), f, g) \<Rightarrow> Abs_pmc_target ((a, f a b'), f, g))"

fun upd2 :: "'b * ('a, 'b) pmc_target \<Rightarrow> ('a, 'b) pmc_target" where
  "upd2 (b, p) =
    (case Rep_pmc_target p of
      ((a', b'), f, g) \<Rightarrow> Abs_pmc_target ((g b a', b), f, g))"

abbreviation l1 :: "('a, ('a, 'b) pmc_target) lens_parms" where
"l1 \<equiv> \<lparr> lens_parms.upd = upd1, lens_parms.proj = proj1, lens_parms.vwb = {x . True}  \<rparr>"

abbreviation l2 :: "('b, ('a, 'b) pmc_target) lens_parms" where
"l2 \<equiv> \<lparr> lens_parms.upd = upd2, lens_parms.proj = proj2, lens_parms.vwb = {x . True}  \<rparr>"

(* need to constrain to compatible f and g (?) *)
abbreviation pmp :: "('a, 'b, ('a, 'b) pmc_target) prod_merge_parms" where
"pmp \<equiv> \<lparr> lens1 = l1, lens2 = l2 \<rparr>"
*)
lemma Coh :
  fixes c c'
  shows "upd1 (proj1 c, upd2 (proj2 c, c')) =
         upd2 (proj2 c, upd1 (proj1 c, c'))"
  apply(case_tac c') apply(clarsimp)
  apply(case_tac c) apply(clarsimp)
  apply(cut_tac y = "((a, b), aa, ba)" in Abs_pmc_target_inverse) apply(clarsimp)
  apply(clarsimp)
  apply(cut_tac y = "((ab, bb), ac, bc)" in Abs_pmc_target_inverse) apply(clarsimp)
  apply(clarsimp)
  apply(cut_tac y = "((ba bb a, bb), aa, ba)" in Abs_pmc_target_inverse)
   apply(clarsimp)
  apply(clarsimp)
  apply(cut_tac y = " ((ab, aa ab b), aa, ba)" in Abs_pmc_target_inverse)
   apply(clarsimp)
  apply(clarsimp)
  apply(cut_tac x = "Abs_pmc_target ((ab, aa ab bb), aa, ba)"
        and y = "Abs_pmc_target ((ba bb ab, bb), aa, ba)" in Rep_pmc_target_inject)
  apply(clarsimp)
  apply(drule_tac x = ab in spec) apply (rotate_tac -1)
  apply(drule_tac x = bb in spec) apply (rotate_tac -1)
  apply(drule_tac x = ab in spec) apply (rotate_tac -1)
  apply(drule_tac x = bb in spec) apply (rotate_tac -1)
  apply(auto)
   defer

  apply(cut_tac x = "Abs_pmc_target ((ab, aa ab b), aa, ba)" in Rep_pmc_target)
  apply(clarsimp)

lemma duh : True
  apply(simp)
  done

lemma extend : 
  shows "\<And> P . True \<Longrightarrow> P \<Longrightarrow> P"
  apply(simp)
  done


interpretation Tryit : Prod_Merge_Total_Spec pmp
  apply(unfold_locales)
            apply(clarsimp) 
           apply(case_tac m1c, clarsimp)
  apply(case_tac "Rep_pmc_target ba") apply(clarsimp)
           apply(cut_tac x = ba in Rep_pmc_target)  apply(clarsimp)
  apply(cut_tac y = "((aa, bb aa b), bb, c)" in Abs_pmc_target_inverse) apply(clarsimp)
           apply(fastforce)

  apply(case_tac c)
  apply(clarsimp)
          apply(cut_tac y = "((a, b), aa, ba)" in Abs_pmc_target_inverse) apply(simp)
          apply(simp)

         apply(case_tac m1m1'c) apply(clarsimp)
         apply(case_tac "Rep_pmc_target c") apply(clarsimp)
  apply(rename_tac boo)
         apply(cut_tac y = "((ba, bb ba b), bb, boo)" in Abs_pmc_target_inverse)
          apply(clarsimp) 
  apply(cut_tac x = c in Rep_pmc_target) apply(clarsimp)

  apply(clarsimp)
         apply(cut_tac x = c in Rep_pmc_target)  apply(clarsimp)

  apply(clarsimp)
(* the problem here is that the functions may differ! *)
  defer
  defer
       defer
       apply(case_tac cc') apply(clarsimp)
       apply(case_tac "Rep_pmc_target ba") apply(clarsimp)
       apply(case_tac "(Rep_pmc_target aa)") apply(clarsimp)
       apply(rename_tac boo1 boo2)

(*
  apply(cut_tac x = "Abs_pmc_target ((c bc a, bc), bb, c)" in Rep_pmc_target)
       apply(clarsimp)
  apply(cut_tac x = "Abs_pmc_target ((ab, bb ab b), bb, c)" in Rep_pmc_target)
       apply(clarsimp)
*)
       apply(cut_tac y = "((ab, bb ab b), bb, c)" in Abs_pmc_target_inverse)
        apply(clarsimp)
        apply(cut_tac x = ba in Rep_pmc_target) apply(clarsimp)
       apply(clarsimp)
       apply(cut_tac y = "((c bc a, bc), bb, c)" in Abs_pmc_target_inverse)
  apply(clarsimp)

        apply(cut_tac x = ba in Rep_pmc_target) apply(clarsimp)
       apply(clarsimp)

        apply(cut_tac x = ba in Rep_pmc_target) apply(clarsimp)
        apply(cut_tac x = aa in Rep_pmc_target) apply(clarsimp)

       apply(cut_tac y = "((ab, bb ab b), bb, c)" in Abs_pmc_target_inverse)
  apply(clarsimp)

        apply(cut_tac x = ba in Rep_pmc_target) apply(clarsimp)
        apply(cut_tac x = aa in Rep_pmc_target) apply(clarsimp)


(* things seem to go off the rails here *)
  apply(cut_tac x = "Abs_pmc_target ((c bc a, bc), bb, c)" in Rep_pmc_target)
  apply(clarsimp)
        apply(cut_tac x = aa in Rep_pmc_target) apply(clarsimp)
        apply(cut_tac x = ba in Rep_pmc_target) apply(clarsimp)
  apply(clarsimp)
       apply(cut_tac y = "((ab, bb ab b), bb, c)" in Abs_pmc_target_inverse)
        apply(clarsimp)
  apply(clarsimp)
  apply(case_tac "Rep_pmc_target
              (Abs_pmc_target
                ((c (snd (fst (Rep_pmc_target aa))) a, snd (fst (Rep_pmc_target aa))), bb, c))")
       apply(clarsimp)
  apply(case_tac " Rep_pmc_target
              (Abs_pmc_target
                ((fst (fst (Rep_pmc_target aa)), bb (fst (fst (Rep_pmc_target aa))) b), bb, c))")
       apply(clarsimp)
       apply(case_tac "(Rep_pmc_target aa)") apply(clarsimp)
        apply(cut_tac x = ba in Rep_pmc_target) apply(clarsimp)
        apply(cut_tac x = aa in Rep_pmc_target) apply(clarsimp)

  apply(cut_tac y = "((c be a, be), bb, c)" in Abs_pmc_target_inverse)
        apply(simp)
  apply(cut_tac y = "((ad, bb ad b), bb, c)" in Abs_pmc_target_inverse)
        apply(simp)
       apply(clarsimp)
  apply(drule_tac x = a in spec) apply(rotate_tac -1)
       apply(drule_tac x = b in spec)
  apply(clarsimp)

  apply(drule_tac x = ad in spec) apply(rotate_tac -1)
  apply(drule_tac x = bc in spec) apply(clarsimp)
  apply(cut_tac y = "((ad, bb ad b), bb, c)" in Abs_pmc_target_inverse)
        apply(simp)
       apply(clarsimp)
       apply(cut_tac x = "(Abs_pmc_target ((ad, bca ad b), bca, ca))" in Rep_pmc_target)
  apply(cut_tac x = "(Abs_pmc_target ((ca bc a, bc), bca, ca))" in Rep_pmc_target)
  apply(clarsimp)
       apply(drule_tac x = ad in spec) apply(rotate_tac -1)
  apply(drule_tac x = bc in spec)
       apply(clarsimp)
  apply(blast)

           apply(drule_tac allI) apply(drule_tac x = ba in spec) apply(clarsimp)
           apply(insert Rep_pmc_target_inverse) apply(drule_tac allI) apply(drule_tac x = ba in spec) apply(clarsimp)

  apply(cut_tac "Abs_pmc_target_inverse") apply(auto)
  apply(simp add: Rep_pmc_target)
  apply(rule_tac "Rep_pmc_target_cases[of ba]")


locale Prod_Merge_Concrete =  
  fixes cross1 :: "'b \<Rightarrow> 'a \<Rightarrow> 'a" 
  fixes cross2 :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"

  assumes Cross11 :
    "cross1 x2 (cross1 x2' x1) = cross1 x2 x1"
  assumes Cross22 :
    "cross2 x1 (cross2 x1' x2) = cross2 x1 x2"
  assumes CrossMatch1 : "cross1 b a = a \<Longrightarrow> cross2 a b = b"
  assumes CrossMatch2 : "cross2 a b = b \<Longrightarrow> cross1 b a = a"

begin

(* we're almost there. just need to figure out how
to make Put21 go through... *)
abbreviation vwb' :: "('a * 'b) set" where
"vwb' \<equiv> {(a, b) . cross1 b a = a \<and> cross2 a b = b  }"

fun proj1' :: "('a * 'b) \<Rightarrow> 'a" where
"proj1' (a, b) = a"

(*
fun proj2' :: "('a * 'b) \<Rightarrow> 'b" where
"proj2' (a, b) = (if (a, b) \<in> vwb' then cross2 a b else b)"
*)

fun proj2' :: "('a * 'b) \<Rightarrow> 'b" where
"proj2' (a, b) = b"

fun upd1' :: "'a * ('a * 'b) \<Rightarrow> 'a * 'b" where
"upd1' (a, a', b') =  
  (if (a', b') \<in> vwb' then (a, cross2 a b') else (a, b'))"

fun upd2' :: "'b * ('a * 'b) \<Rightarrow> 'a * 'b" where
"upd2' (b, a', b') = 
  (if (a', b') \<in> vwb' then (cross1 b a', b) else (a', b))"


abbreviation lp1 :: "('a, ('a * ('b))) lens_parms"
  where
  "lp1 \<equiv> \<lparr> upd = upd1', proj = proj1', vwb = vwb' \<rparr>"

abbreviation lp2 :: "('b, ('a * ('b))) lens_parms"
  where
  "lp2 \<equiv> \<lparr> upd = upd2', proj = proj2', vwb = vwb' \<rparr>"

abbreviation pmp :: "('a, 'b, ('a * 'b)) prod_merge_parms"
  where
"pmp \<equiv> \<lparr> lens1 = lp1, lens2 = lp2 \<rparr>"

lemma Cross12 :
    "cross1 (cross2 x1 x2) x1 = x1"
  apply(insert CrossMatch2[of x1 "cross2 x1 x2"])
  apply(simp add: Cross22)
  done

lemma Cross21 :
    "cross2 (cross1 x2 x1) x2 = x2"
  apply (insert CrossMatch1[of x2 "cross1 x2 x1"])
  apply(simp add:Cross11)
  done

(*
lemma Cross11 :
  "cross1 x2 (cross1 x2 x1) = cross1 x2 x1"
  apply(insert Cross21)
*)
(*
fun proj1' ::
  "(('a * 'b) + ('b * 'a)) \<Rightarrow> 'a" where
"proj1' (Inl (a, b)) = a"
| "proj1' (Inr (b, a)) = cross1 b a"

fun proj2' ::
  "(('a * 'b) + ('b * 'a)) \<Rightarrow> 'b" where
"proj2' (Inl (a, b)) = cross2 a b"
| "proj2' (Inr (b, a)) = b"

(* idea: should we try to keep the same constructor Inl/Inr? *)
fun up1' ::
  "'a * (('a * 'b) + ('b * 'a)) \<Rightarrow> (('a * 'b) + ('b * 'a))"
  where
"up1' (a, Inl (a', b')) =
  ((Inl (a, b')))"
| "up1' (a, Inr (b', a')) =
    (if a = cross1 b' a' then Inr (b', a') else Inl (a, cross2 a b'))"

fun up2' ::
  "'b * (('a * 'b) + ('b * 'a)) \<Rightarrow> (('a * 'b) + ('b * 'a))"
  where
"up2' (b, Inl (a', b')) =
  (if (cross2 a' b' = b) then Inl (a', b')
  else (Inr (b, a'))) "
| "up2' (b, Inr (b', a')) =
    (if b = cross2 a' b' then Inr (b', a')
    else Inr (b, a'))"

abbreviation lp1 :: "('a, ('a * 'b) + ('b * 'a)) lens_parms"
  where
  "lp1 \<equiv> \<lparr> upd = up1', proj = proj1' \<rparr>"

abbreviation lp2 :: "('b, ('a * 'b) + ('b * 'a)) lens_parms"
  where
  "lp2 \<equiv> \<lparr> upd = up2', proj = proj2' \<rparr>"

abbreviation pmp :: "('a, 'b, ('a * 'b) + ('b * 'a)) prod_merge_parms"
  where
"pmp \<equiv> \<lparr> lens1 = lp1, lens2 = lp2 \<rparr>"
end
*)
(*
fun proj1' ::
  "('a * 'b * ('a + 'b)) \<Rightarrow> 'a" where
"proj1' (a', b', Inl a) = a"
| "proj1' (a', b', Inr b) = cross1 b a'"

fun proj2' ::
  "('a * 'b * ('a + 'b)) \<Rightarrow> 'b" where
"proj2' (a', b', Inl a) = cross2 a b'"
| "proj2' (a', b', Inr b) = b"

fun up1' ::
  "'a * ('a * 'b * ('a + 'b)) \<Rightarrow> ('a * 'b * ('a + 'b))"
  where
"up1' (a, (a'', b'', Inl a')) =
  (if (a = a') then (a', b'', Inl a')
  else (a, b'', Inl a))"
| "up1' (a, (a'', b'', Inr b')) =
  (if (a = cross1 b' a'') then (a'', b'', Inr b')
   else (a'', b', Inl a))"

(* WIP *)
fun up2' ::
  "'b * ('a * 'b * ('a + 'b)) \<Rightarrow> ('a * 'b * ('a + 'b))"
  where
"up2' (b, (a'', b'', Inl a')) =
  (if (b = cross2 a' b'') then (a'', b'', Inl a')
  else (a', b, Inr b))"
| "up2' (b, (a'', b'', Inr b')) =
  (if (b = b') then (a'', b'', Inr b')
   else (a'', b, Inr b))"

abbreviation lp1 :: "('a, ('a * 'b * ('a + 'b))) lens_parms"
  where
  "lp1 \<equiv> \<lparr> upd = up1', proj = proj1' \<rparr>"

abbreviation lp2 :: "('b, ('a * 'b * ('a + 'b))) lens_parms"
  where
  "lp2 \<equiv> \<lparr> upd = up2', proj = proj2' \<rparr>"

abbreviation pmp :: "('a, 'b, ('a * 'b * ('a + 'b))) prod_merge_parms"
  where
"pmp \<equiv> \<lparr> lens1 = lp1, lens2 = lp2 \<rparr>"
end
*)
(*
fun valid :: "('a * 'b) \<Rightarrow> bool" where
"valid (a, b) = (cross1 b a = a \<and> cross2 a b = b)"

fun proj1' ::
  "('a * 'b) \<Rightarrow> 'a" where
"proj1' (a, b) = a"

fun proj2' ::
  "('a * 'b) \<Rightarrow> 'b" where
"proj2' (a, b) = cross2 a b"

(*
fun proj2' ::
  "('a * 'b) \<Rightarrow> 'b" where
"proj2' (a, b) = b"
*)

fun up1' ::
  "'a * ('a * 'b) \<Rightarrow> ('a * 'b)"
  where
"up1' (a, (a', b')) = (a, b')"

(*
fun up1' ::
  "'a * ('a * 'b) \<Rightarrow> ('a * 'b)"
  where
"up1' (a, (a', b')) = 
  (a, b')"
*)
(* WIP *)

(*
fun up2' ::
  "'b * ('a * 'b) \<Rightarrow> ('a * 'b)"
  where
"up2' (b, (a', b')) = 
  (if b = b' then (a', b') else (cross1 b a', b))"
*)
(*
fun up2' ::
  "'b * ('a * 'b) \<Rightarrow> ('a * 'b)"
  where
"up2' (b, (a', b')) = 
  (if b = cross2 a' b' then (a', b') else
  (if cross1 b' a' = cross1 b a' then (a', b')
    else (cross1 b a', b)))"
*)
fun up2' ::
  "'b * ('a * 'b) \<Rightarrow> ('a * 'b)"
  where
"up2' (b, (a', b')) = 
  (if cross1 b a' = cross1 b' a' then (a', b') else
  (cross1 b a', b))"
(*
fun up2' ::
  "'b * ('a * 'b) \<Rightarrow> ('a * 'b)"
  where
"up2' (b, (a', b')) = (a', b)"
*)
(*
fun up2' ::
  "'b * ('a * 'b) \<Rightarrow> ('a * 'b)"
  where
"up2' (b, (a', b')) = 
  (if cross1 b' a' = a' \<and> cross2 a' b' = b' then (cross1 b a', b)
  else (a', b))"
*)
abbreviation lp1 :: "('a, ('a * 'b)) lens_parms"
  where
  "lp1 \<equiv> \<lparr> upd = up1', proj = proj1' \<rparr>"

abbreviation lp2 :: "('b, ('a * 'b)) lens_parms"
  where
  "lp2 \<equiv> \<lparr> upd = up2', proj = proj2' \<rparr>"

abbreviation pmp :: "('a, 'b, ('a * 'b)) prod_merge_parms"
  where
"pmp \<equiv> \<lparr> lens1 = lp1, lens2 = lp2 \<rparr>"
end
*)
(*
fun proj1' ::
  "('a * ('a \<Rightarrow> 'b)) \<Rightarrow> 'a" where
"proj1' (a, f) = a"

fun proj2' ::
  "('a * ('a \<Rightarrow> 'b)) \<Rightarrow> 'b" where
"proj2' (a, f) = f a"

(*
fun proj2' ::
  "('a * 'b) \<Rightarrow> 'b" where
"proj2' (a, b) = b"
*)

fun up1' ::
  "'a * ('a * ('a \<Rightarrow> 'b)) \<Rightarrow> ('a * ('a \<Rightarrow> 'b))"
  where
"up1' (a, (a', f)) = (a, f)"

fun up2' ::
  "'b * ('a * ('a \<Rightarrow> 'b)) \<Rightarrow> ('a * ('a \<Rightarrow> 'b))"
  where
"up2' (b, (a', f)) =
  (cross1 b a', \<lambda> ax . cross2 (cross1 b a') (f ax))"
(*
fun up2' ::
  "'b * ('a * 'b) \<Rightarrow> ('a * 'b)"
  where
"up2' (b, (a', b')) = (a', b)"
*)
(*
fun up2' ::
  "'b * ('a * 'b) \<Rightarrow> ('a * 'b)"
  where
"up2' (b, (a', b')) = 
  (if cross1 b' a' = a' \<and> cross2 a' b' = b' then (cross1 b a', b)
  else (a', b))"
*)
abbreviation lp1 :: "('a, ('a * ('a \<Rightarrow> 'b))) lens_parms"
  where
  "lp1 \<equiv> \<lparr> upd = up1', proj = proj1' \<rparr>"

abbreviation lp2 :: "('b, ('a * ('a \<Rightarrow> 'b))) lens_parms"
  where
  "lp2 \<equiv> \<lparr> upd = up2', proj = proj2' \<rparr>"

abbreviation pmp :: "('a, 'b, ('a * ('a \<Rightarrow> 'b))) prod_merge_parms"
  where
"pmp \<equiv> \<lparr> lens1 = lp1, lens2 = lp2 \<rparr>"
*)
end


sublocale Prod_Merge_Concrete \<subseteq> Prod_Merge_Total_Spec pmp
  apply(unfold_locales)
            apply(clarsimp)
        apply(simp add: Cross11 Cross22 Cross21 Cross12)

          apply(clarsimp)
         apply(clarsimp)
         apply(clarsimp)  
         apply(simp add: Cross11 Cross22 Cross21 Cross12)
  apply(clarsimp)
        apply(simp add: Cross11 Cross22 Cross21 Cross12)

       apply(clarsimp)
      apply(simp add: Cross11 Cross22 Cross21 Cross12)

      apply(clarsimp)
  apply(clarsimp)
        apply(simp add: Cross11 Cross22 Cross21 Cross12)

  apply(clarsimp)

   apply(simp)
  apply(case_tac m1m2cc') apply(simp)
   apply(clarsimp)
        apply(simp add: Cross11 Cross22 Cross21 Cross12)

  apply(simp)

  apply(case_tac m2m1cc') apply(simp) apply(case_tac c) apply(simp)
  apply(simp add: Cross11 Cross22 Cross21 Cross12)
  done
end